FROM snazzybucket/idris2:latest

RUN apt update && apt install -y git curl rlwrap
RUN curl -fsSL https://deb.nodesource.com/setup_16.x | bash - && apt install -y nodejs