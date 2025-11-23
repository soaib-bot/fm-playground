import os
import subprocess
import tempfile


def run_dafny(code: str) -> str:
    tmp_file = tempfile.NamedTemporaryFile(mode="w", delete=False, suffix=".dfy")
    tmp_file.write(code)
    tmp_file.close()
    try:
        command = ["dafny", "verify", tmp_file.name]
        result = subprocess.run(command, capture_output=True, text=True, timeout=10)
        os.remove(tmp_file.name)
        # if result.returncode != 0:
        #     return result.stderr
        return result.stdout
    except subprocess.TimeoutExpired:
        os.remove(tmp_file.name)
        return "Timeout expired"