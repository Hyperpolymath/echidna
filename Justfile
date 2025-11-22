# Justfile for ECHIDNA
# PRIMARY build system (not Make)

# Default recipe
default:
    @just --list

# Build all components
build: build-rust build-julia build-ui
    @echo "✓ ECHIDNA build complete"

# Build Rust core
build-rust:
    @echo "Building Rust core..."
    cargo build --release

# Build Julia components
build-julia:
    @echo "Building Julia components..."
    julia --project=src/julia -e 'using Pkg; Pkg.instantiate()'

# Build ReScript UI
build-ui:
    @echo "Building ReScript UI..."
    cd src/rescript && npm install && npm run res:build

# Run all tests
test: test-rust test-julia test-proofs
    @echo "✓ All tests passed"

# Test Rust components
test-rust:
    @echo "Testing Rust..."
    cargo test --all-features

# Test Julia ML components
test-julia:
    @echo "Testing Julia..."
    julia --project=src/julia test/runtests.jl

# Test proof examples
test-proofs:
    @echo "Testing proof validation..."
    ./scripts/test-proofs.sh

# Run all quality checkers
check: check-licenses check-security check-format check-julia
    @echo "✓ All quality checks passed"

# Check license compliance (REUSE)
check-licenses:
    @echo "Checking license compliance..."
    reuse lint

# Security scanning (Trivy)
check-security:
    @echo "Scanning for security issues..."
    trivy fs --severity HIGH,CRITICAL .

# Check code formatting
check-format:
    @echo "Checking Rust formatting..."
    cargo fmt -- --check
    cargo clippy -- -D warnings

# Check Julia code quality
check-julia:
    @echo "Checking Julia code..."
    julia --project=src/julia -e 'using Aqua, JET; ...'

# Format code
fmt:
    @echo "Formatting code..."
    cargo fmt

# Clean build artifacts
clean:
    @echo "Cleaning build artifacts..."
    cargo clean
    rm -rf target/
    rm -rf src/julia/Manifest.toml
    cd src/rescript && npm run res:clean
    rm -rf src/rescript/node_modules

# Build container (Podman)
container-build:
    @echo "Building container with Podman..."
    podman build -f Containerfile -t echidna:latest .

# Run container
container-run:
    @echo "Running ECHIDNA container..."
    podman run -it echidna:latest

# Deploy templates to Quill repo
deploy-templates:
    @echo "Deploying RSR/CCCP templates..."
    ./scripts/deploy-templates.sh

# Initialize project
setup:
    @echo "Setting up ECHIDNA project..."
    ./scripts/setup.sh

# Customize placeholders
customize:
    @echo "Customizing template placeholders..."
    ./scripts/customize.sh

# Run proof examples for all provers
proof-examples PROVER="all":
    @echo "Running proof examples for {{PROVER}}..."
    ./scripts/run-proofs.sh {{PROVER}}

# Benchmark neural solver
bench:
    @echo "Running benchmarks..."
    cargo bench

# Generate documentation
docs:
    @echo "Generating documentation..."
    cargo doc --no-deps --open
    julia --project=src/julia -e 'using Documenter; ...'

# Development server
dev:
    @echo "Starting development server..."
    cargo watch -x 'run --bin echidna'

# Development server for UI
dev-ui:
    @echo "Starting ReScript UI development server..."
    cd src/rescript && npm run dev

# Build and serve UI
serve-ui:
    @echo "Serving ReScript UI..."
    cd src/rescript && npm run serve

# Watch ReScript compilation
watch-ui:
    @echo "Watching ReScript files..."
    cd src/rescript && npm run res:dev

# Install development dependencies
install-dev-deps:
    @echo "Installing development dependencies..."
    cargo install cargo-watch
    cargo install wasm-pack
    julia --project=src/julia -e 'using Pkg; Pkg.add(["Aqua", "JET", "Coverage"])'
