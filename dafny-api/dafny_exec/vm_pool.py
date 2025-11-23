import os
import subprocess
import tempfile
import json
import threading
import time
import queue
from typing import Optional

FIRECRACKER_BIN = "/usr/local/bin/firecracker"
KERNEL_PATH = "/opt/vm-resources/vmlinux"
ROOTFS_PATH = "/opt/vm-resources/rootfs.ext4"

class VMInstance:
    """Represents a single VM instance that can be reused"""
    def __init__(self, vm_id: int):
        self.vm_id = vm_id
        self.tmpdir = None
        self.process = None
        self.socket_path = None
        self.code_img = None
        self.output_img = None
        self.is_busy = False
        self.created_at = time.time()
        
    def prepare(self):
        """Prepare the VM directories and images"""
        self.tmpdir = tempfile.mkdtemp(prefix=f"vm_{self.vm_id}_")
        
        # Prepare code drive (will be populated per request)
        self.code_img = os.path.join(self.tmpdir, "code.ext4")
        subprocess.run(["dd", "if=/dev/zero", f"of={self.code_img}", "bs=1M", "count=2"], 
                       check=True, capture_output=True)
        subprocess.run(["mkfs.ext4", "-F", "-O", "^64bit,^metadata_csum,^metadata_csum_seed", self.code_img], 
                       check=True, capture_output=True)
        
        # Prepare output drive
        self.output_img = os.path.join(self.tmpdir, "output.ext4")
        subprocess.run(["dd", "if=/dev/zero", f"of={self.output_img}", "bs=1M", "count=2"], 
                       check=True, capture_output=True)
        subprocess.run(["mkfs.ext4", "-F", self.output_img], 
                       check=True, capture_output=True)
        
        self.socket_path = os.path.join(self.tmpdir, f"firecracker_{self.vm_id}.socket")
        
    def start(self):
        """Start the VM (boots to a paused state waiting for code)"""
        config_path = os.path.join(self.tmpdir, "config.json")
        log_path = os.path.join(self.tmpdir, "firecracker.log")
        
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
        
        # Start Firecracker in background
        with open(log_path, "w") as log_file:
            self.process = subprocess.Popen(
                [FIRECRACKER_BIN, "--api-sock", self.socket_path, "--config-file", config_path],
                stdout=log_file,
                stderr=subprocess.STDOUT
            )
    
    def execute_code(self, code: str) -> str:
        """Execute code in this VM instance"""
        self.is_busy = True
        try:
            # Mount code image and write code
            code_mount = os.path.join(self.tmpdir, "code_mount")
            os.makedirs(code_mount, exist_ok=True)
            subprocess.run(["mount", "-o", "loop", self.code_img, code_mount], 
                          check=True, capture_output=True)
            
            try:
                code_file = os.path.join(code_mount, "program.dfy")
                with open(code_file, "w") as f:
                    f.write(code)
            finally:
                subprocess.run(["umount", code_mount], check=True, capture_output=True)
            
            # Wait for VM to complete (will reboot and restart)
            self.process.wait(timeout=30)
            
            # Read output
            result = subprocess.run(
                ["debugfs", "-R", "cat result.txt", self.output_img], 
                capture_output=True, text=True
            )
            
            if "File not found" in result.stderr:
                return "Error: Result file not found in VM output"
            
            return result.stdout
            
        except subprocess.TimeoutExpired:
            if self.process:
                self.process.kill()
            return "Error: Execution timed out"
        finally:
            self.is_busy = False
    
    def cleanup(self):
        """Clean up VM resources"""
        if self.process and self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.process.kill()
        
        if self.tmpdir and os.path.exists(self.tmpdir):
            subprocess.run(["rm", "-rf", self.tmpdir], capture_output=True)


class VMPool:
    """Pool of warm VMs ready for execution"""
    def __init__(self, pool_size: int = 3, max_vm_age: int = 300):
        self.pool_size = pool_size
        self.max_vm_age = max_vm_age  # Max age in seconds before recycling
        self.available_vms = queue.Queue(maxsize=pool_size)
        self.all_vms = []
        self.lock = threading.Lock()
        self.running = False
        self.maintenance_thread = None
        
    def start(self):
        """Start the VM pool"""
        self.running = True
        
        # Pre-create VMs
        for i in range(self.pool_size):
            vm = self._create_vm(i)
            self.all_vms.append(vm)
            self.available_vms.put(vm)
        
        # Start maintenance thread
        self.maintenance_thread = threading.Thread(target=self._maintain_pool, daemon=True)
        self.maintenance_thread.start()
    
    def _create_vm(self, vm_id: int) -> VMInstance:
        """Create and prepare a new VM instance"""
        vm = VMInstance(vm_id)
        vm.prepare()
        # Note: We don't actually start Firecracker here since it will exit after one run
        # Instead, we just prepare the filesystem images
        return vm
    
    def _maintain_pool(self):
        """Background thread to maintain the pool"""
        while self.running:
            time.sleep(10)  # Check every 10 seconds
            
            with self.lock:
                # Remove old VMs
                current_time = time.time()
                for vm in self.all_vms[:]:
                    if current_time - vm.created_at > self.max_vm_age and not vm.is_busy:
                        vm.cleanup()
                        self.all_vms.remove(vm)
                        
                        # Create replacement
                        new_vm = self._create_vm(len(self.all_vms))
                        self.all_vms.append(new_vm)
                        try:
                            self.available_vms.put_nowait(new_vm)
                        except queue.Full:
                            pass
    
    def execute(self, code: str, timeout: int = 30) -> str:
        """Execute code using a VM from the pool"""
        vm = None
        try:
            # Get an available VM (wait up to 5 seconds)
            vm = self.available_vms.get(timeout=5)
            
            # Execute the code (this will start, run, and shutdown the VM)
            result = vm.execute_code(code)
            
            return result
            
        except queue.Empty:
            return "Error: No VMs available in pool"
        finally:
            if vm:
                # Return VM to pool (will be recycled on next maintenance cycle)
                # Since Firecracker exits after each run, we need to recreate
                with self.lock:
                    vm.cleanup()
                    new_vm = self._create_vm(vm.vm_id)
                    self.all_vms.append(new_vm)
                try:
                    self.available_vms.put_nowait(new_vm)
                except queue.Full:
                    new_vm.cleanup()
    
    def stop(self):
        """Stop the VM pool and cleanup all VMs"""
        self.running = False
        if self.maintenance_thread:
            self.maintenance_thread.join(timeout=5)
        
        with self.lock:
            for vm in self.all_vms:
                vm.cleanup()
            self.all_vms.clear()
            
            # Clear the queue
            while not self.available_vms.empty():
                try:
                    self.available_vms.get_nowait()
                except queue.Empty:
                    break


# Global pool instance
_vm_pool: Optional[VMPool] = None
_pool_lock = threading.Lock()

def get_vm_pool(pool_size: int = 3) -> VMPool:
    """Get or create the global VM pool"""
    global _vm_pool
    with _pool_lock:
        if _vm_pool is None:
            _vm_pool = VMPool(pool_size=pool_size)
            _vm_pool.start()
        return _vm_pool

def run_in_vm_pool(code: str) -> str:
    """Execute code using the VM pool"""
    pool = get_vm_pool()
    return pool.execute(code)
