#!/usr/bin/env bash

# Configure Mistral Vibe for this development environment.
# - Installs the Mistral Vibe VS Code extension if missing.
# - Ensures required TOML entries exist in the Mistral config file.

set -euo pipefail
IFS=$'\n\t'

log() {
  echo "[setup-mistral-vibe] $*"
}

error() {
  echo "[setup-mistral-vibe] ERROR: $*" >&2
}

ensure_code_cli() {
  if ! command -v code >/dev/null 2>&1; then
    error "The 'code' CLI is not available in PATH."
    error "In VS Code, run: Command Palette -> 'Shell Command: Install code command in PATH'."
    exit 1
  fi
}

resolve_config_file() {
  if [ -n "${MISTRAL_CONFIG_FILE:-}" ]; then
    echo "$MISTRAL_CONFIG_FILE"
    return
  fi

  echo "$HOME/.vibe/config.toml"
}

install_vibe_vscode_extension_if_missing() {
  local extension_id="mistralai.mistral-vibe-code"

  if code --list-extensions | grep -Fxq "$extension_id"; then
    log "VS Code extension '$extension_id' is already installed."
    return
  fi

  log "Installing VS Code extension '$extension_id'..."
  code --install-extension "$extension_id"
  log "Installed VS Code extension '$extension_id'."
}

ensure_installed_agents_contains_lean() {
  local config_file=$1

  perl -0777 -i -pe '
    my $added = 0;
    if (/^\s*installed_agents\s*=\s*\[(.*?)\]/ms) {
      my $block = $&;
      my $items = $1;
      if ($items !~ /"lean"/) {
        my $replacement = $block;
        if ($replacement =~ /\[\s*\]/s) {
          $replacement =~ s/\[\s*\]/[\n    "lean",\n]/s;
        } else {
          $replacement =~ s/\]\s*$/    "lean",\n]/s;
        }
        s/\Q$block\E/$replacement/s;
        $added = 1;
      }
    } else {
      $_ .= "\ninstalled_agents = [\n    \"lean\",\n]\n";
      $added = 1;
    }
    END {
      if ($added) {
        print STDERR "[setup-mistral-vibe] Added installed_agents entry for lean.\n";
      }
    }
  ' "$config_file"
}

ensure_lean_lsp_mcp_server() {
  local config_file=$1

  if grep -Eq '^[[:space:]]*name[[:space:]]*=[[:space:]]*"lean-lsp"' "$config_file"; then
    log "lean-lsp MCP server already configured."
    return
  fi

  cat >>"$config_file" <<'EOF'

[[mcp_servers]]
name = "lean-lsp"
transport = "stdio"
command = "uvx"
args = [
    "lean-lsp-mcp",
]
tool_timeout_sec = 600
EOF
  log "Added lean-lsp MCP server configuration."
}

main() {
  ensure_code_cli
  install_vibe_vscode_extension_if_missing

  local config_file
  config_file=$(resolve_config_file)
  mkdir -p "$(dirname "$config_file")"
  touch "$config_file"

  ensure_installed_agents_contains_lean "$config_file"
  ensure_lean_lsp_mcp_server "$config_file"

  log "Setup complete. Config updated at: $config_file"
}

main "$@"