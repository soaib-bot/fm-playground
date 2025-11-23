import os
import subprocess
import tempfile
import json

FIRECRACKER_BIN = "/usr/local/bin/firecracker"
# These paths must match where we put them in the Dockerfile
KERNEL_PATH = "/opt/vm-resources/vmlinux"
ROOTFS_PATH = "/opt/vm-resources/rootfs.ext4"


def run_in_vm(code: str, operation: str = "verify") -> str:
    # Check if resources exist
    if not os.path.exists(KERNEL_PATH) or not os.path.exists(ROOTFS_PATH):
        return "Error: VM resources (kernel/rootfs) not found."

    if not os.path.exists("/dev/kvm"):
        return "Error: /dev/kvm not found. Hardware virtualization is required for Firecracker."

    # Create a temporary directory for this run
    with tempfile.TemporaryDirectory() as tmpdir:
        # Prepare Code Drive (ext4 instead of ISO since kernel doesn't support iso9660)
        code_img = os.path.join(tmpdir, "code.ext4")

        # Create small ext4 image (2MB is enough for code)
        subprocess.run(
            ["dd", "if=/dev/zero", f"of={code_img}", "bs=1M", "count=2"],
            check=True,
            capture_output=True,
        )
        subprocess.run(
            [
                "mkfs.ext4",
                "-F",
                "-O",
                "^64bit,^metadata_csum,^metadata_csum_seed",
                code_img,
            ],
            check=True,
            capture_output=True,
        )

        # Mount it temporarily to copy the code file
        code_mount = os.path.join(tmpdir, "code_mount")
        os.makedirs(code_mount, exist_ok=True)
        subprocess.run(
            ["mount", "-o", "loop", code_img, code_mount],
            check=True,
            capture_output=True,
        )

        try:
            code_file = os.path.join(code_mount, "program.dfy")
            with open(code_file, "w") as f:
                f.write(code)
            # Write operation type
            operation_file = os.path.join(code_mount, "operation.txt")
            with open(operation_file, "w") as f:
                f.write(operation)
        finally:
            subprocess.run(["umount", code_mount], check=True, capture_output=True)

        # Prepare Output Drive (ext4)
        output_img = os.path.join(tmpdir, "output.ext4")
        # Create 2MB empty file
        subprocess.run(
            ["dd", "if=/dev/zero", f"of={output_img}", "bs=1M", "count=2"],
            check=True,
            capture_output=True,
        )
        # Format as ext4 (force with -F)
        subprocess.run(["mkfs.ext4", "-F", output_img], check=True, capture_output=True)

        # Create Firecracker Config
        config_path = os.path.join(tmpdir, "config.json")

        # Log file for Firecracker
        log_path = os.path.join(tmpdir, "firecracker.log")

        config = {
            "boot-source": {
                "kernel_image_path": KERNEL_PATH,
                "boot_args": "console=ttyS0 noapic reboot=k panic=1 pci=off nomodules root=/dev/vda rw rootfstype=ext4 init=/sbin/custom-init",
            },
            "drives": [
                {
                    "drive_id": "rootfs",
                    "path_on_host": ROOTFS_PATH,
                    "is_root_device": True,
                    "is_read_only": True,
                },
                {
                    "drive_id": "code",
                    "path_on_host": code_img,
                    "is_root_device": False,
                    "is_read_only": True,
                },
                {
                    "drive_id": "output",
                    "path_on_host": output_img,
                    "is_root_device": False,
                    "is_read_only": False,
                },
            ],
            "machine-config": {
                "vcpu_count": 1,
                "mem_size_mib": 512,  # Balance between speed and Dafny's memory needs
            },
            "logger": {
                "log_path": log_path,
                "level": "Debug",
                "show_level": True,
                "show_log_origin": True,
            },
        }

        with open(config_path, "w") as f:
            json.dump(config, f)

        # Run Firecracker
        # Firecracker requires an API socket even when using --config-file
        # We provide a socket path in the temp directory
        socket_path = os.path.join(tmpdir, "firecracker.socket")

        try:
            # We capture stdout/stderr to avoid polluting logs, but they might be useful for debugging
            # We can also redirect them to the log file
            with open(log_path, "w") as log_file:
                subprocess.run(
                    [
                        FIRECRACKER_BIN,
                        "--api-sock",
                        socket_path,
                        "--config-file",
                        config_path,
                    ],
                    check=True,
                    timeout=30,
                    stdout=log_file,
                    stderr=subprocess.STDOUT,
                )
        except subprocess.TimeoutExpired:
            # VM timed out but might have produced output - try to read it anyway
            pass
        except subprocess.CalledProcessError as e:
            # Read the log file to get the error
            error_msg = f"Error: Firecracker failed (Exit Code {e.returncode})"
            if os.path.exists(log_path):
                with open(log_path, "r") as f:
                    error_msg += f"\nLog:\n{f.read()}"
            return error_msg
        except FileNotFoundError:
            return "Error: Firecracker binary not found"

        # Read Output
        # Use debugfs to read the file from the unmounted image
        try:
            # Try to read boot.log first for debugging
            boot_log = subprocess.run(
                ["debugfs", "-R", "cat boot.log", output_img],
                capture_output=True,
                text=True,
            )

            # debugfs -R "cat result.txt" output.ext4
            # Note: debugfs might output the file content to stdout.
            result = subprocess.run(
                ["debugfs", "-R", "cat result.txt", output_img],
                capture_output=True,
                text=True,
            )
            # debugfs returns 0 even if file not found sometimes, but prints error to stderr
            if "File not found" in result.stderr:
                debug_info = ""
                if boot_log.stdout:
                    debug_info = f"\n\nBoot log:\n{boot_log.stdout}"

                # Also include firecracker log
                if os.path.exists(log_path):
                    with open(log_path, "r") as f:
                        log_content = f.read()
                        if log_content:
                            # Look for virtio and block device mentions
                            virtio_lines = [
                                line
                                for line in log_content.split("\n")
                                if "virtio" in line.lower()
                                or " vd" in line
                                or "block" in line.lower()
                            ]
                            if virtio_lines:
                                debug_info += (
                                    f"\n\nVirtio/block-related boot messages:\n"
                                    + "\n".join(virtio_lines[:15])
                                )
                            debug_info += f"\n\nFirecracker log (last 800 chars):\n{log_content[-800:]}"

                return f"Error: Result file not found in VM output{debug_info}"

            return result.stdout
        except Exception as e:
            return f"Error processing output: {str(e)}"
