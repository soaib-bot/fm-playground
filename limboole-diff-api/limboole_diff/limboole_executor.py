import os
import re
import platform
import concurrent.futures
import subprocess
import tempfile

system = platform.system().lower()

# Get the directory where this script is located
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
# Go up one level to the limboole-diff-api directory
BASE_DIR = os.path.dirname(SCRIPT_DIR)


def get_executable_path() -> str:
    """Detect OS and return the correct Limboole executable path."""
    system = platform.system().lower()
    if "windows" in system:
        return os.path.join(BASE_DIR, "lib", "limboole.exe")
    elif "linux" in system:
        return os.path.join(BASE_DIR, "lib", "limboole-linux-x86.exe")
    elif "darwin" in system or "mac" in system:
        return os.path.join(BASE_DIR, "lib", "limbooleAPE.exe")
    else:
        raise OSError(f"Unsupported OS: {system}")


LIMBOOLE_EXE = get_executable_path()


MAX_CONCURRENT_REQUESTS = 10
executor = concurrent.futures.ThreadPoolExecutor(max_workers=MAX_CONCURRENT_REQUESTS)


def run_limboole(code: str, check_sat: bool = True) -> str:
    tmp_file = tempfile.NamedTemporaryFile(mode="w", delete=False, suffix=".limboole")
    tmp_file.write(code)
    tmp_file.close()

    try:
        if check_sat:
            # APE has a special polyglot format.
            # Running from shell automatically handles it.
            if system == "darwin" or system == "mac":
                command = ["sh", LIMBOOLE_EXE, "-s", tmp_file.name]
            else:
                command = [LIMBOOLE_EXE, "-s", tmp_file.name]
        else:
            if system == "darwin" or system == "mac":
                command = ["sh", LIMBOOLE_EXE, tmp_file.name]
            else:
                command = [LIMBOOLE_EXE, tmp_file.name]
        result = subprocess.run(command, capture_output=True, text=True, timeout=5)
        os.remove(tmp_file.name)
        if result.returncode != 0:
            return prettify_error(result.stderr)
        return result.stdout
    except subprocess.TimeoutExpired:
        os.remove(tmp_file.name)
        return "Timeout expired"
    except Exception as e:
        # Ensure cleanup even on unexpected errors
        if os.path.exists(tmp_file.name):
            os.remove(tmp_file.name)
        raise e


def prettify_error(stderr: str) -> str:
    modified_stderr = re.sub(r"^.*\.limboole:", "<stdin>:", stderr)
    return modified_stderr


def process_commands(code: str, check_sat: bool = True) -> str:
    future = executor.submit(run_limboole, code, check_sat)
    return future.result()
