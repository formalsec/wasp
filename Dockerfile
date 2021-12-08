# syntax=docker/dockerfile:1
FROM ubuntu:20.04
ENV BASE=/home/wasp/robust-concolic-exec
ENV Z3_VERSION=4.8.1

RUN apt-get update  && DEBIAN_FRONTEND=noninteractive apt-get install -y \
    sudo ranger vim make llvm clang lld opam wabt libgmp-dev python3-pip && \
    useradd -m wasp && \
    echo wasp:wasp | chpasswd && \
    cp /etc/sudoers /etc/sudoers.bak && \
    echo 'wasp ALL=(root) NOPASSWD: ALL' >> /etc/sudoers

COPY --chown=wasp:wasp . /home/wasp/robust-concolic-exec

USER wasp
WORKDIR /home/wasp

# Install opam
RUN opam init -y --disable-sandboxing && \
    eval $(opam env) && \
    opam switch create ocaml-base-compiler.4.08.1 && \
    eval $(opam env) && \
    echo 'test -r /home/wasp/.opam/opam-init/init.sh && . /home/wasp/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true' >> /home/wasp/.bashrc

# Instal required OCaml packages
RUN opam install -y extlib batteries z3=$Z3_VERSION

ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:/home/wasp/.opam/ocaml-base-compiler.4.08.1/lib/z3/"

# wasm-ld -> wasm-ld-10
RUN sudo ln -sf /usr/bin/wasm-ld-10 /usr/bin/wasm-ld

# Build WASP and libc
RUN eval $(opam env) && make -C "${BASE}/wasp" && \
    python3 -m pip install pycparser && \
    make -C "${BASE}/wasp-c/lib"

ENV PATH="${PATH}:${BASE}/wasp:${BASE}/wasp-c/bin"
