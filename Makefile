##############################################################################
# Makefile for installing the Curry front end
##############################################################################

# the root directory of the installation
export ROOT=$(CURDIR)
# binary directory and executables
export BINDIR=$(ROOT)/bin
# The frontend binary
export CYMAKE = $(BINDIR)/curry-frontend

# install front end (if sources are present):
.PHONY: frontend
frontend:
	stack install --allow-different-user --local-bin-path $(BINDIR)

.PHONY: clean
clean:
	stack clean

.PHONY: cleanall
cleanall:
	stack clean --full
	rm -f $(CYMAKE) && rm -rf bin

.PHONY: runtests
runtests:
	stack test
