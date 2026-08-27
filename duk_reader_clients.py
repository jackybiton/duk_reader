from __future__ import annotations

import os


os.environ["DUK_CUSTOMER_EDITION"] = "1"

from duk_reader import main


if __name__ == "__main__":
    main()
