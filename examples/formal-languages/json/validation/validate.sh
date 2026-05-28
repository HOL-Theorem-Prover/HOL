#!/bin/bash
set -euo pipefail

HOLMAKE="../../../../bin/Holmake"

# Check if validation tests directory exists
if [ ! -d "JSONTestSuite/test_parsing" ]; then
    git clone --depth 1 https://github.com/nst/JSONTestSuite.git
fi

"$HOLMAKE"
./validate
