import os
import subprocess
import tempfile
from .vm import run_in_vm
from .vm_pool_fast import run_with_pooled_resources


def run_dafny(code: str, operation: str = "verify") -> str:
    use_microvm = os.getenv("USE_MICROVM", "false").lower() == "true"
    use_vm_pool = os.getenv("USE_VM_POOL", "false").lower() == "true"
    
    if use_microvm:
        if use_vm_pool:
            return run_with_pooled_resources(code, operation)
        else:
            return run_in_vm(code, operation)

    tmp_file = tempfile.NamedTemporaryFile(mode="w", delete=False, suffix=".dfy")
    tmp_file.write(code)
    tmp_file.close()
    try:
        command = ["dafny", operation, tmp_file.name]
        result = subprocess.run(command, capture_output=True, text=True, timeout=10)
        os.remove(tmp_file.name)
        # if result.returncode != 0:
        #     return result.stderr
        return result.stdout
    except subprocess.TimeoutExpired:
        os.remove(tmp_file.name)
        return "Timeout expired"