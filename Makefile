##############################################################################
# Makefile for installing the Curry front end
##############################################################################

# Essential system dependencies
STACKBIN := $(shell which stack)

ifeq ($(STACKBIN),)
$(error Please make sure that 'stack' (The Haskell Stack build tool) is on your PATH or specify it explicitly by passing 'make STACKBIN=...')
endif

# the root directory of the installation
export ROOT=$(CURDIR)
# binary directory and executables
export BINDIR=$(ROOT)/bin
# The frontend binary
export FRONTEND = $(BINDIR)/curry-frontend
# The stack root directory
STACKROOT = $(ROOT)/.stack
# The actual stack command with local root directory
STACK = $(STACKBIN) --stack-root $(STACKROOT)

# install front end (if sources are present):
.PHONY: frontend
frontend:
	$(STACK) install --local-bin-path $(BINDIR)

.PHONY: clean
clean:
	$(STACK) clean

# clean components only used for installation, i.e., `stack` related stuff
.PHONY: cleaninstall
cleaninstall:
	$(STACK) clean --full
	rm -rf $(STACKROOT)

.PHONY: cleanall
cleanall: cleaninstall
	rm -f $(FRONTEND) && rm -rf bin

.PHONY: runtests
runtests:
	$(STACK) test
