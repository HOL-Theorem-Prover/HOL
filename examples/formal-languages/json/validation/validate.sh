#!/bin/bash
set -euo pipefail

cd "$(dirname "$0")"

HOLMAKE="../../../../bin/Holmake"

if [ ! -d "JSONTestSuite/test_parsing" ]; then
    git clone --depth 1 https://github.com/nst/JSONTestSuite.git
fi

"$HOLMAKE"
./validate
