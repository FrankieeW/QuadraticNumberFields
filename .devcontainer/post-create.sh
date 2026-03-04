#!/bin/bash
# Post-create script for devcontainer
set -e

# Install Elan (Lean version manager)
if ! command -v elan &> /dev/null; then
    curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
    source ~/.elan/env
fi

# Install Ruby for Jekyll site
if command -v apt-get &> /dev/null; then
    apt-get update && apt-get install -y ruby ruby-dev build-essential
    gem install jekyll bundler
fi

echo "Devcontainer setup complete!"
