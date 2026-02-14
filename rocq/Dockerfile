FROM rocq/rocq-prover:9.1

# Pin coq-lsp to the 9.1-compatible version (without pin, opam resolves
# to 0.1.8+8.16 which removes Rocq 9.1 and compiles Coq 8.16 from source)
RUN opam update \
 && opam unpin ocamlfind \
 && opam install -y coq-lsp.0.2.5+9.1

# Add lwt and logs for pet-server (TCP mode)
RUN opam install -y lwt logs

# Create workspace for Rocq proofs (base image runs as non-root user)
WORKDIR /home/coq
RUN mkdir -p proofs
WORKDIR /home/coq/proofs

# pet-server listens on 8765 by default
EXPOSE 8765

CMD ["opam", "exec", "--", "pet-server", "--address=0.0.0.0"]
