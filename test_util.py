import os

os.environ["CLICOLOR_FORCE"] = "1"
CONSOLE_WIDTH = 100


class Color:
    PURPLE = "\033[95m"
    CYAN = "\033[96m"
    DARKCYAN = "\033[36m"
    BLUE = "\033[94m"
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    RED = "\033[91m"
    BOLD = "\033[1m"
    UNDERLINE = "\033[4m"
    END = "\033[0m"


class TestCase:
    def __init__(self, name):
        self.name = name
        print(f"{self.name}", end=": ")

    def expected_pass(self, stdout: str = ""):
        print(
            " " * (CONSOLE_WIDTH - len(self.name) - 16)
            + f"{Color.GREEN}{Color.BOLD}EXPECTED PASS{Color.END}"
        )
        if stdout:
            print("\n".join("    " + s for s in stdout.strip().splitlines()))
            print("=" * CONSOLE_WIDTH)

    def expected_error(self, stderr: str):
        print(
            " " * (CONSOLE_WIDTH - len(self.name) - 16)
            + f"{Color.GREEN}{Color.BOLD}EXPECTED ERROR{Color.END}"
        )
        if stderr:
            print("\n".join("    " + s for s in stderr.strip().splitlines()))
            print("=" * CONSOLE_WIDTH)

    def unexpected_pass(self, stderr: str):
        print(
            " " * (CONSOLE_WIDTH - len(self.name) - 18)
            + f"{Color.RED}{Color.BOLD}UNEXPECTED PASS{Color.END}"
        )
        if stderr:
            print("\n".join("    " + s for s in stderr.strip().splitlines()))
            print("=" * CONSOLE_WIDTH)

    def unexpected_error(self, stderr: str):
        print(
            " " * (CONSOLE_WIDTH - len(self.name) - 18)
            + f"{Color.RED}{Color.BOLD}UNEXPECTED ERROR{Color.END}"
        )
        print("\n".join("    " + s for s in stderr.strip().splitlines()))
        print("=" * CONSOLE_WIDTH)
