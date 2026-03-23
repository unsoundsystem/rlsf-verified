# Build:  docker build -f misc/docker/Dockerfile -t rlsf-verified .
# Run:    docker run --rm rlsf-verified          # runs misc/check.sh
# Tests:  docker run --rm rlsf-verified cargo test -p rlsf-verified-tests
#
# NOTE: Run from the repository root so the build context includes all sources.

FROM ubuntu:24.04

ARG VERUS_COMMIT=e97969ef173a7165673ffbb48738c4a1b975daeb

ENV DEBIAN_FRONTEND=noninteractive

# Basic build dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential \
        ca-certificates \
        cmake \
        curl \
        git \
        libssl-dev \
        pkg-config \
        python3 \
        singular \
        unzip \
    && rm -rf /var/lib/apt/lists/*

# Install Rust via rustup
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | \
    sh -s -- -y --default-toolchain none
ENV PATH="/root/.cargo/bin:${PATH}"

# Clone Verus and patch vstd: u64_trailing_zeros is 'closed' upstream but
# project code needs to reveal it for by(compute) on SPEC_SIZE_SIZE_MASK.
# The patch changes it to 'opaque' (hidden but revealable).
COPY misc/docker/patch_vstd.py /tmp/patch_vstd.py
RUN git clone https://github.com/verus-lang/verus.git /opt/verus \
    && cd /opt/verus \
    && git checkout ${VERUS_COMMIT} \
    && python3 /tmp/patch_vstd.py source/vstd/std_specs/bits.rs \
    && cd source \
    && bash tools/get-z3.sh \
    && cargo install --locked --path /opt/verus/tools/vargo \
    && vargo build --release --features singular \
    && rustup default "$(rustup toolchain list | head -1 | awk '{print $1}')"

ENV VERUS_PATH=/opt/verus/source/target-verus/release/verus
ENV VERUS_SINGULAR_PATH=/usr/bin/Singular

WORKDIR /work
COPY . /work

# check.sh expects verus at ../../verus relative to misc/
# i.e. /work/misc/../../verus -> /verus
RUN ln -s /opt/verus /verus

# Pre-fetch Cargo dependencies so later runs are faster
RUN cargo fetch || true

CMD ["bash", "misc/check.sh"]
