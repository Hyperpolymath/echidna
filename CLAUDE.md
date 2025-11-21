# CLAUDE.md

This document provides guidelines and context for working with Claude Code on the echidna project.

## Project Overview

**echidna** - [Brief description of the project - to be updated]

## Repository Structure

```
echidna/
├── .git/           # Git repository
└── CLAUDE.md       # This file
```

## Working with Claude Code

### General Guidelines

1. **Code Quality**: Maintain high code quality standards with proper error handling, tests, and documentation
2. **Git Workflow**: Follow conventional commit messages and keep commits atomic
3. **Security**: Be vigilant about security vulnerabilities (XSS, SQL injection, command injection, etc.)
4. **Dependencies**: Document all dependencies and their purposes

### Development Workflow

When working on features or fixes:

1. Create feature branches with descriptive names (prefix with `claude/` for Claude Code branches)
2. Write clear, concise commit messages
3. Test changes thoroughly before committing
4. Update documentation as needed

### Commit Message Format

Follow conventional commit format:
- `feat:` - New features
- `fix:` - Bug fixes
- `docs:` - Documentation changes
- `refactor:` - Code refactoring
- `test:` - Adding or updating tests
- `chore:` - Maintenance tasks

Example: `feat: add user authentication module`

### Code Style

- Use consistent formatting throughout the codebase
- Include comments for complex logic
- Keep functions small and focused
- Use meaningful variable and function names

### Testing

- Write tests for new features
- Ensure existing tests pass before committing
- Include both unit and integration tests where appropriate

### Documentation

- Update README.md for user-facing changes
- Document API endpoints and interfaces
- Include inline comments for complex algorithms
- Keep this CLAUDE.md updated with project-specific guidelines

## Project-Specific Context

### Tech Stack

[To be documented as project develops]

### Key Dependencies

[To be documented as dependencies are added]

### Architecture

[To be documented as architecture is defined]

### Known Issues

[Document any known issues or limitations]

## Useful Commands

```bash
# [Add project-specific commands as they become relevant]
# Example:
# npm install    - Install dependencies
# npm test       - Run tests
# npm run build  - Build the project
```

## Resources

- [Project Documentation - TBD]
- [API Reference - TBD]
- [Contributing Guidelines - TBD]

## Notes for Claude Code

### Priorities

1. Code correctness and security
2. Clear, maintainable code
3. Comprehensive testing
4. Thorough documentation

### Constraints

- Always verify file paths before operations
- Use parallel tool calls when operations are independent
- Prefer specialized tools over bash commands for file operations
- Use the Task tool for complex, multi-step operations

### Special Considerations

[Add any project-specific considerations for Claude Code]

---

**Last Updated**: 2025-11-21
**Maintained By**: Project team
