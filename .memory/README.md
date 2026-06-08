# Shared Memory Vault

This directory contains an Obsidian-compatible vault shared between Claude Code and OpenCode AI systems. Memories created by either system are accessible to both.

## Multi-System Usage

This vault is intentionally shared across AI systems:
- Both Claude Code and OpenCode can read all memories
- Both systems can create and update memories
- Memory IDs include timestamps for collision resistance
- Index files are regenerated from filesystem state

### MCP Server Considerations

Only one AI system should use MCP-based search at a time:
- Claude Code: Uses WebSocket port 22360
- OpenCode: Uses REST API port 27124

Both systems fall back to grep-based search when MCP is unavailable, which works safely in concurrent scenarios.

## Directory Structure

```
.memory/
+-- .obsidian/           # Obsidian configuration
+-- 00-Inbox/            # Quick capture for new memories
+-- 10-Memories/         # Stored memory entries
+-- 20-Indices/          # Navigation and organization
+-- 30-Templates/        # Memory entry templates
```

## Adding Memories

Use the `/learn` command:
- `/learn "text to remember"` - Add text content
- `/learn /path/to/file.md` - Add file content

The command will:
1. Parse the input
2. Generate a unique memory ID (collision-resistant format)
3. Present a preview with checkbox options
4. Allow you to add new, update existing, edit, or skip

## Git Workflow

**What to commit**:
- All `.md` files in the vault
- Templates and indices
- This README

**What to ignore** (in `.gitignore`):
- `.obsidian/` directory (user-specific Obsidian settings)
- `*.sqlite` files (search indexes)
- Plugin directories

## MCP Server Setup

For advanced features (search, retrieval), configure the MCP server:

1. Open Obsidian app
2. Open this `.memory/` as a vault
3. Install the appropriate MCP plugin for your system
4. Configure MCP server in your project settings

See the memory-setup.md in your system's context directory for detailed instructions.

## Naming Conventions

Memory files follow the pattern:
```
MEM-{semantic-slug}.md
```

Example: `MEM-project-code-patterns.md`, `MEM-project-code-patterns.md`

The MEM- prefix is preserved for grep discoverability (`grep -r "MEM-" .memory/`).

## Template Format

Memory entries use YAML frontmatter:
```yaml
---
title: "Python HTTP Best Practices"
created: 2026-03-06
tags: python, http, configuration
topic: "python/http"
source: "user input"
modified: 2026-03-06
---
```

Note: The `id:` field has been removed. Filenames serve as unique identifiers.

## Best Practices

- Use descriptive first lines for better titles
- Review index.md regularly for navigation
- Commit memories to git for version history
- Use tags for better organization
- Link related memories using `[[filename]]` syntax
