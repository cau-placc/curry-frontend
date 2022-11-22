##############################################################################
# Makefile for installing the Curry front end
##############################################################################

# the root directory of the installation
export ROOT=$(CURDIR)
# binary directory and executables
export BINDIR=$(ROOT)/bin
# The frontend binary
export FRONTEND = $(BINDIR)/curry-frontend
# The stack binary
STACK = stack

# install front end (if sources are present):
.PHONY: frontend
frontend:
	$(STACK) install --local-bin-path $(BINDIR)

.PHONY: clean
clean:
	$(STACK) clean

.PHONY: cleanall
cleanall:
	$(STACK) clean --full
	rm -f $(FRONTEND) && rm -rf bin

.PHONY: runtests
runtests:
	$(STACK) test
