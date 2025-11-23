import os
import subprocess
import tempfile
import json
import threading
import queue
from typing import Optional

FIRECRACKER_BIN = "/usr/local/bin/firecracker"
KERNEL_PATH = "/opt/vm-resources/vmlinux"
ROOTFS_PATH = "/opt/vm-resources/rootfs.ext4"


class PreparedVMResources:
    """Pre-prepared VM filesystem images ready for code injection"""
    def __init__(self, resource_id: int):
        self.resource_id = resource_id
        self.tmpdir = tempfile.mkdtemp(prefix=f"vm_ready_{resource_id}_")
        self.code_img = os.path.join(self.tmpdir, "code.ext4")
        self.output_img = os.path.join(self.tmpdir, "output.ext4")
        self.code_mount = os.path.join(self.tmpdir, "code_mount")
        
        # Pre-create filesystem images
        subprocess.run(["dd", "if=/dev/zero", f"of={self.code_img}", "bs=1M", "count=2"], 
                       check=True, capture_output=True)
        subprocess.run(["mkfs.ext4", "-F", "-O", "^64bit,^metadata_csum,^metadata_csum_seed", self.code_img], 
                       check=True, capture_output=True)
        
        subprocess.run(["dd", "if=/dev/zero", f"of={self.output_img}", "bs=1M", "count=2"], 
                       check=True, capture_output=True)
        subprocess.run(["mkfs.ext4", "-F", self.output_img], 
                       check=True, capture_output=True)
        
        os.makedirs(self.code_mount, exist_ok=True)
    
    def inject_code_and_run(self, code: str, operation: str = "verify") -> str:
        """Inject code and run VM with specified operation (verify or run)"""
        # Mount, write code, unmount
        subprocess.run(["mount", "-o", "loop", self.code_img, self.code_mount], 
                      check=True, capture_output=True)
        try:
            code_file = os.path.join(self.code_mount, "program.dfy")
            with open(code_file, "w") as f:
                f.write(code)
            # Write operation type
            operation_file = os.path.join(self.code_mount, "operation.txt")
            with open(operation_file, "w") as f:
                f.write(operation)
        finally:
            subprocess.run(["umount", self.code_mount], check=True, capture_output=True)
        
        # Configure and run Firecracker
        config_path = os.path.join(self.tmpdir, "config.json")
        log_path = os.path.join(self.tmpdir, "firecracker.log")
        socket_path = os.path.join(self.tmpdir, "firecracker.socket")
        
        config = {
            "boot-source": {
                "kernel_image_path": KERNEL_PATH,
                "boot_args": "console=ttyS0 noapic reboot=k panic=1 pci=off nomodules root=/dev/vda rw rootfstype=ext4 init=/sbin/custom-init"
            },
            "drives": [
                {
                    "drive_id": "rootfs",
                    "path_on_host": ROOTFS_PATH,
                    "is_root_device": True,
                    "is_read_only": True
                },
                {
                    "drive_id": "code",
                    "path_on_host": self.code_img,
                    "is_root_device": False,
                    "is_read_only": True
                },
                {
                    "drive_id": "output",
                    "path_on_host": self.output_img,
                    "is_root_device": False,
                    "is_read_only": False
                }
            ],
            "machine-config": {
                "vcpu_count": 1,
                "mem_size_mib": 512
            },
            "logger": {
                "log_path": log_path,
                "level": "Error"
            }
        }
        
        with open(config_path, "w") as f:
            json.dump(config, f)
        
        try:
            with open(log_path, "w") as log_file:
                subprocess.run([FIRECRACKER_BIN, "--api-sock", socket_path, "--config-file", config_path], 
                              check=True, timeout=30, stdout=log_file, stderr=subprocess.STDOUT)
        except subprocess.TimeoutExpired:
            pass  # VM timed out, try to read output anyway
        except subprocess.CalledProcessError as e:
            pass  # VM errored, try to read output anyway
        
        # Read output
        result = subprocess.run(
            ["debugfs", "-R", "cat result.txt", self.output_img], 
            capture_output=True, text=True
        )
        
        if "File not found" in result.stderr:
            return "Error: Result file not found in VM output"
        
        return result.stdout
    
    def cleanup(self):
        """Clean up resources"""
        if os.path.exists(self.tmpdir):
            subprocess.run(["rm", "-rf", self.tmpdir], capture_output=True)


class VMResourcePool:
    """Pool of pre-created VM resources (filesystem images)"""
    def __init__(self, pool_size: int = 3, pre_warm: bool = True):
        self.pool_size = pool_size
        self.available = queue.Queue(maxsize=pool_size)
        self.lock = threading.Lock()
        
        # Pre-create resources if pre_warm is enabled
        if pre_warm:
            for i in range(pool_size):
                resources = PreparedVMResources(i)
                self.available.put(resources)
    
    def execute(self, code: str, operation: str = "verify") -> str:
        """Execute code using pooled resources with specified operation (verify or run)"""
        resources = None
        try:
            # Get available resources (non-blocking)
            resources = self.available.get(timeout=1)
            
            # Execute
            result = resources.inject_code_and_run(code, operation)
            
            return result
            
        except queue.Empty:
            # No resources available, create temporary one
            temp_resources = PreparedVMResources(-1)
            try:
                return temp_resources.inject_code_and_run(code, operation)
            finally:
                temp_resources.cleanup()
        finally:
            if resources:
                # Return to pool
                try:
                    self.available.put_nowait(resources)
                except queue.Full:
                    resources.cleanup()
    
    def cleanup_all(self):
        """Clean up all resources"""
        while not self.available.empty():
            try:
                resources = self.available.get_nowait()
                resources.cleanup()
            except queue.Empty:
                break


# Global pool
_resource_pool: Optional[VMResourcePool] = None
_pool_lock = threading.Lock()

def get_resource_pool(pool_size: int = 3) -> VMResourcePool:
    """Get or create the global resource pool"""
    global _resource_pool
    with _pool_lock:
        if _resource_pool is None:
            _resource_pool = VMResourcePool(pool_size=pool_size)
        return _resource_pool

def run_with_pooled_resources(code: str, operation: str = "verify") -> str:
    """Execute code using pooled resources"""
    pool = get_resource_pool()
    return pool.execute(code, operation)
