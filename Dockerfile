# syntax=docker/dockerfile:1
FROM ubuntu:20.04
ENV BASE=/home/wasp
ENV Z3_VERSION=4.8.1

LABEL org.opencontainers.image.source https://github.com/wasp-platform/wasp

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y \
    sudo ranger vim make llvm clang lld opam wabt libgmp-dev python3-pip \
    git npm curl lcov clang-tidy gcc-multilib \
    && useradd -m wasp \
    && echo wasp:wasp | chpasswd \
    && cp /etc/sudoers /etc/sudoers.bak \
    && echo 'wasp ALL=(root) NOPASSWD: ALL' >> /etc/sudoers

COPY --chown=wasp:wasp . /home/wasp/

USER wasp
WORKDIR /home/wasp

# Install opam
RUN opam init -y --disable-sandboxing \
    && eval $(opam env) \
    && opam switch create 4.14.0 \
    && eval $(opam env) \
    && echo 'test -r /home/wasp/.opam/opam-init/init.sh && . /home/wasp/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true' >> /home/wasp/.bashrc

# Instal required OCaml packages
RUN cd "${BASE}" && opam install -y . --deps-only

ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:/home/wasp/.opam/default/lib/z3/"

# wasm-ld -> wasm-ld-10
RUN sudo ln -sf /usr/bin/wasm-ld-10 /usr/bin/wasm-ld

# Build WASP and libc
RUN eval $(opam env) && cd "${BASE}" \
    && dune build && dune install \
    && python3 -m pip install pycparser numpy tsbuilder \
    && make -C "${BASE}/share/libc"

# Get test suites
RUN git clone https://github.com/wasp-platform/Collections-C.git "${BASE}/Collections-C"
RUN git clone https://github.com/wasp-platform/Test-Comp.git "${BASE}/Test-Comp"
RUN git clone https://gitlab.com/sosy-lab/software/test-suite-validator.git "${BASE}/test-suite-validator"
RUN git clone https://github.com/wasp-platform/aws-cryptosdk-c.git "${BASE}/aws-encryption-sdk"

# Gillian
#RUN git clone https://github.com/GillianPlatform/Gillian.git "${BASE}/Gillian"
#RUN git clone https://github.com/GillianPlatform/collections-c-for-gillian.git "${BASE}/collections-c-for-gillian"
#RUN sudo npm install -g esy@0.6.6 --unsafe-perm && \
#    cd ${BASE}/Gillian && git checkout 2cb5f8d73baf7f7a811b0be6044d533a62c3f50 && \
#    esy install && esy
