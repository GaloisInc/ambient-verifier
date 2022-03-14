FROM ubuntu:20.04
ENV TZ=America/Los_Angeles
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone
RUN apt update && \
    apt install -y \
      build-essential \
      curl \
      git \
      libffi7 \
      libffi-dev \
      libgmp10 \
      libgmp-dev \
      libncurses5 \
      libncurses-dev \
      libtinfo5 \
      locales \
      openssh-client \
      software-properties-common \
      unzip \
      zlib1g-dev && \
    locale-gen en_US.UTF-8

ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

RUN mkdir -p /home/solvers
WORKDIR /home/solvers
RUN curl -o solvers.zip -sL "https://github.com/GaloisInc/what4-solvers/releases/download/snapshot-20210917/ubuntu-18.04-bin.zip"
RUN unzip solvers.zip && \
    rm solvers.zip && \
    chmod +x * && \
    cp cvc4 /usr/local/bin/cvc4 && \
    cp z3 /usr/local/bin/z3 && \
    cp yices /usr/local/bin/yices && \
    cp yices-smt2 /usr/local/bin/yices-smt2

RUN curl -L https://downloads.haskell.org/~ghcup/0.1.17.5/x86_64-linux-ghcup-0.1.17.5 -o /usr/bin/ghcup && chmod +x /usr/bin/ghcup
RUN mkdir -p /root/.ghcup && ghcup --version && ghcup install cabal 3.6.2.0 && ghcup install ghc 8.10.7 && ghcup set ghc 8.10.7

######################################################################
ENV PATH="/root/.ghcup/bin:${PATH}"
RUN cabal update
RUN mkdir -p /home/src
COPY . /home/src
WORKDIR /home/src
RUN ln -sf cabal.project.dist cabal.project
RUN cabal configure -w ghc-8.10.7 --enable-tests && \
    cabal build exe:ambient-verifier test:ambient-tests -j5

RUN cp $(cabal list-bin exe:ambient-verifier) /usr/local/bin/ambient-verifier && \
    cp $(cabal list-bin test:ambient-tests) /usr/local/bin/ambient-tests

FROM ubuntu:20.04
RUN apt update && \
    apt install -y \
      libgmp10 \
      zlib1g \
      zlibc
COPY --from=0 /usr/local/bin/ambient-verifier \
              /usr/local/bin/ambient-tests \
              /usr/local/bin/cvc4 \
              /usr/local/bin/z3 \
              /usr/local/bin/yices \
              /usr/local/bin/yices-smt2 \
              /usr/local/bin/
COPY --from=0 /home/src/tests /tests
EXPOSE 5000
ENV ADDR=0.0.0.0
ENTRYPOINT ["/usr/local/bin/ambient-verifier"]
