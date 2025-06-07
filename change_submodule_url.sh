#!/bin/bash

# Usage: ./change-submodule-origin.sh <submodule-path> <new-origin-url>

SUBMODULE_PATH="$1"
NEW_URL="$2"

if [[ -z "$SUBMODULE_PATH" || -z "$NEW_URL" ]]; then
    echo "Usage: $0 <submodule-path> <new-origin-url>"
    exit 1
fi

cd "$SUBMODULE_PATH" || exit 1
git remote set-url origin "$NEW_URL"
cd - > /dev/null

# Also update in superproject .gitmodules (optional but recommended)
git config -f .gitmodules submodule."$SUBMODULE_PATH".url "$NEW_URL"

echo "Submodule '$SUBMODULE_PATH' origin changed to: $NEW_URL"
