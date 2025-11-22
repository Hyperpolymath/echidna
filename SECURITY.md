<!--
SPDX-License-Identifier: MIT AND Palimpsest-0.6
SPDX-FileCopyrightText: 2024-2025 ECHIDNA Project Contributors
-->

# Security Policy

## Supported Versions

The following versions of ECHIDNA are currently being supported with security updates:

| Version | Supported          |
| ------- | ------------------ |
| 0.1.x   | :white_check_mark: |
| < 0.1   | :x:                |

## Security Principles

ECHIDNA follows these security principles:

1. **Defense in Depth**: Multiple layers of security controls
2. **Least Privilege**: Minimal necessary permissions
3. **Secure by Default**: Safe default configurations
4. **Fail Securely**: Graceful degradation on errors
5. **Complete Mediation**: All access requests are checked
6. **Transparency**: Open communication about security issues

## Reporting a Vulnerability

We take the security of ECHIDNA seriously. If you believe you have found a security vulnerability, please report it to us as described below.

### Where to Report

**DO NOT** report security vulnerabilities through public GitLab issues.

Instead, please report them via email to:

**security@echidna-project.org** (Replace with actual security contact)

### What to Include

Please include the following information in your report:

- Type of vulnerability (e.g., buffer overflow, SQL injection, XSS, etc.)
- Full paths of source file(s) related to the vulnerability
- Location of the affected source code (tag/branch/commit or direct URL)
- Any special configuration required to reproduce the issue
- Step-by-step instructions to reproduce the issue
- Proof-of-concept or exploit code (if possible)
- Impact of the issue, including how an attacker might exploit it

### Response Timeline

- **Initial Response**: Within 48 hours of report
- **Status Update**: Within 7 days with initial assessment
- **Patch Development**: Timeline provided based on severity
- **Public Disclosure**: Coordinated with reporter after patch release

### Security Disclosure Process

1. **Report Received**: Security team acknowledges receipt
2. **Assessment**: Team assesses severity and impact
3. **Development**: Patch is developed and tested
4. **Notification**: Security advisory prepared
5. **Release**: Patch released with advisory
6. **Recognition**: Reporter credited (if desired)

## Security Best Practices

### For Users

1. **Keep Updated**: Always use the latest stable version
2. **Verify Downloads**: Check signatures and checksums
3. **Review Configs**: Audit security-related configurations
4. **Monitor Logs**: Watch for suspicious activity
5. **Report Issues**: Report any security concerns promptly

### For Contributors

1. **Input Validation**: Always validate and sanitize inputs
2. **Output Encoding**: Properly encode outputs to prevent injection
3. **Authentication**: Use strong authentication mechanisms
4. **Authorization**: Implement proper access controls
5. **Cryptography**: Use well-tested cryptographic libraries
6. **Dependencies**: Keep dependencies updated and audited
7. **Secrets**: Never commit secrets or credentials
8. **Code Review**: All code must be reviewed before merging

## Security Features

### Current Security Measures

- **REUSE Compliance**: All code properly licensed and attributed
- **Trivy Scanning**: Automated vulnerability scanning via CI/CD
- **Aqua.jl**: Julia dependency security analysis
- **Cargo Audit**: Rust dependency vulnerability checking
- **Podman**: Container isolation with rootless mode support
- **SPDX Headers**: Clear license and copyright information

### Planned Security Enhancements

- **Code Signing**: Digital signatures for releases
- **SBOM Generation**: Software Bill of Materials for dependencies
- **Fuzzing**: Automated fuzz testing for parsers
- **SAST/DAST**: Static and dynamic security analysis
- **Dependency Pinning**: Locked dependency versions
- **Security Hardening**: Container and binary hardening

## Vulnerability Severity

We use the CVSS (Common Vulnerability Scoring System) v3.1 to assess severity:

| Score | Severity | Response Time |
|-------|----------|---------------|
| 9.0-10.0 | Critical | 24 hours |
| 7.0-8.9  | High     | 7 days   |
| 4.0-6.9  | Medium   | 30 days  |
| 0.1-3.9  | Low      | 90 days  |

## Security Updates

Security updates are released as:

- **Critical**: Immediate patch release
- **High**: Next patch release (within 7 days)
- **Medium**: Next minor release (within 30 days)
- **Low**: Next major/minor release (within 90 days)

## Security Advisories

Security advisories are published at:

- **GitLab**: https://gitlab.com/non-initiate/rhodinised/quill/-/security/advisories
- **Email**: Subscribers to security@echidna-project.org
- **RSS**: Security advisory feed (when available)

## Scope

### In Scope

The following are in scope for security reports:

- **Core Libraries**: Rust, Julia, ReScript code
- **Prover Backends**: All 12 theorem prover integrations
- **Build System**: Justfile, CI/CD pipelines
- **Containers**: Containerfile and Podman configurations
- **Dependencies**: Third-party libraries and tools

### Out of Scope

The following are typically not accepted:

- Denial of Service (DoS) without proven impact
- Social engineering attacks
- Issues in third-party dependencies (report to upstream)
- Theoretical vulnerabilities without PoC
- Issues requiring physical access
- Issues in unsupported versions

## Threat Model

### Assets

- **Source Code**: Intellectual property and implementation
- **User Data**: Proof scripts and theorem libraries
- **Credentials**: API keys and authentication tokens
- **Build Artifacts**: Compiled binaries and containers

### Threats

- **Code Injection**: Malicious code execution via prover input
- **Data Exfiltration**: Unauthorized access to user proofs
- **Supply Chain**: Compromised dependencies
- **Container Escape**: Breaking out of Podman containers
- **Denial of Service**: Resource exhaustion attacks

### Mitigations

- Input validation and sanitization
- Principle of least privilege
- Dependency security scanning
- Container security hardening
- Rate limiting and resource quotas

## Security Tooling

### Required Tools

- **Trivy**: Container and filesystem vulnerability scanning
- **cargo-audit**: Rust dependency auditing
- **Aqua.jl**: Julia package security analysis
- **REUSE**: License compliance verification

### Recommended Tools

- **cargo-clippy**: Rust linter with security checks
- **JET.jl**: Julia static analysis
- **Semgrep**: Pattern-based security scanning
- **Bandit**: Security linting (if Python used - should not be!)

## Contact

For security-related questions or concerns:

- **Email**: security@echidna-project.org (Replace with actual contact)
- **PGP Key**: Available at https://keys.openpgp.org (when available)
- **GitLab**: @echidna-security (when available)

## Acknowledgments

We thank the following researchers and security professionals for responsibly disclosing vulnerabilities:

- *No vulnerabilities reported yet*

---

**Version**: 1.0
**Last Updated**: 2025-11-22
**Next Review**: 2026-05-22
