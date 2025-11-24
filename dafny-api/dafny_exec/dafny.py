import os
import subprocess
import tempfile
import json


def run_in_gvisor(code: str) -> str:
    """Run Dafny code in a sandboxed Docker container (with gVisor if available)"""
    
    # Create a temporary directory for this execution
    # Use shared directory that's mounted from host
    shared_tmp = "/tmp/dafny-exec"
    os.makedirs(shared_tmp, exist_ok=True)
    tmpdir = tempfile.mkdtemp(prefix="dafny_", dir=shared_tmp)
    try:
        # Write the code to a file
        code_file = os.path.join(tmpdir, "program.dfy")
        with open(code_file, "w") as f:
            f.write(code)
        
        os.chmod(code_file, 0o644)
        os.chmod(tmpdir, 0o755)
        
        # Prepare the dafny command - copy to /tmp for writable access
        dafny_cmd = f"cp /input/program.dfy /tmp/ && cd /tmp && dafny run program.dfy"
        
        # DEBUG:
        # Check if gVisor runtime is available
        # runtime_check = subprocess.run(
        #     ["docker", "info"],
        #     capture_output=True,
        #     text=True
        # )
        # use_gvisor = "runsc" in runtime_check.stdout
        
        docker_args = [
            "docker", "run",
            "--rm",
            "--runtime=runsc",  # gVisor runtime for sandboxing
            "--memory=2g",  # Increased memory for C# compilation
            "--memory-swap=2g",  # Prevent swap usage
            "--cpus=1",  # Increased CPU limit
            "--pids-limit=100",  # Increased process limit for compilation
            "-v", f"{tmpdir}:/input:ro",  # Mount code as read-only
            "--tmpfs", "/tmp:rw,exec,size=500m",  # Larger tmpfs for compilation artifacts
        ]
        
        # Only restrict network for verify operations
        docker_args.extend(["--network=none"])
        
        docker_args.extend([
            "dafny-gvisor",  # Image name
            "sh", "-c", dafny_cmd
        ])
        
        try:
            result = subprocess.run(
                docker_args,
                capture_output=True,
                text=True,
                timeout=30
            )
            return result.stdout + result.stderr
        except subprocess.TimeoutExpired:
            return "Execution timeout"
        except Exception as e:
            return f"Error: {str(e)}"
    finally:
        import shutil
        try:
            shutil.rmtree(tmpdir)
        except Exception:
            pass


def run_dafny(code: str) -> str:
    use_gvisor = os.getenv("USE_GVISOR", "false").lower() == "true"
    
    if use_gvisor:
        return run_in_gvisor(code)
    
    # Fallback to direct execution
    tmp_file = tempfile.NamedTemporaryFile(mode="w", delete=False, suffix=".dfy")
    tmp_file.write(code)
    tmp_file.close()
    try:
        command = ["dafny", "run", tmp_file.name]
        result = subprocess.run(command, capture_output=True, text=True, timeout=10)
        os.remove(tmp_file.name)
        return result.stdout
    except subprocess.TimeoutExpired:
        os.remove(tmp_file.name)
        return "Timeout expired"
    
def verify_dafny(code: str) -> str:
    tmp_file = tempfile.NamedTemporaryFile(mode="w", delete=False, suffix=".dfy")
    tmp_file.write(code)
    tmp_file.close()
    try:
        command = ["dafny", "verify", tmp_file.name]
        result = subprocess.run(command, capture_output=True, text=True, timeout=10)
        os.remove(tmp_file.name)
        return result.stdout
    except subprocess.TimeoutExpired:
        os.remove(tmp_file.name)
        return "Timeout expired"