# SPDX-License-Identifier: MIT OR Palimpsest-0.6
# SPDX-FileCopyrightText: 2025 ECHIDNA Project Contributors

FROM rust:1.83-slim-bookworm AS builder

WORKDIR /build

RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    libreadline-dev \
    && rm -rf /var/lib/apt/lists/*

COPY Cargo.toml Cargo.lock* ./
COPY src/ src/

RUN cargo build --release

FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /build/target/release/echidna /usr/local/bin/echidna

ENTRYPOINT ["echidna"]
CMD ["--help"]
