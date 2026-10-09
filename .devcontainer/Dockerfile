# Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Fabrizio Montesi

FROM mcr.microsoft.com/devcontainers/base:ubuntu

RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    ca-certificates \
    curl \
    ripgrep \
    && rm -rf /var/lib/apt/lists/*

# Install uv + uvx globally for Python CLI tooling (e.g., lean-lsp-mcp).
RUN curl -LsSf https://astral.sh/uv/install.sh | env UV_INSTALL_DIR=/usr/local/bin sh

USER vscode
WORKDIR /home/vscode

ENV PATH="/home/vscode/.elan/bin:/home/vscode/.local/bin:${PATH}"

# Install elan
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

# Install the Lean LSP MCP server
RUN uv tool install lean-lsp-mcp
