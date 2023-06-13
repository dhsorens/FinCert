all: concert theory
.PHONY: all

concert:
	+@make -C FinCert-ConCert-fork/utils
	+@make -C FinCert-ConCert-fork/execution
.PHONY: concert

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

theory: concert CoqMakefile
	+@make -f CoqMakefile
.PHONY: theory

clean: CoqMakefile
	+@make -f CoqMakefile clean
	+@make -C FinCert-ConCert-fork/utils clean
	+@make -C FinCert-ConCert-fork/execution clean
	rm -f CoqMakefile
.PHONY: clean

install: CoqMakefile
	+@make -f CoqMakefile install
.PHONY: install

uninstall: CoqMakefile
	+@make -f CoqMakefile uninstall
.PHONY: uninstall

# Forward most things to Coq makefile. Use 'force' to make this phony.
%: CoqMakefile force
	+@make -f CoqMakefile $@
force: ;

# Do not forward these files
Makefile _CoqProject: ;

html: all
	rm -rf docs
	mkdir docs
	coqdoc --html --interpolate --parse-comments \
		--with-header FinCert-ConCert-fork/extra/header.html --with-footer FinCert-ConCert-fork/extra/footer.html \
		--toc \
		--external https://plv.mpi-sws.org/coqdoc/stdpp stdpp \
		--external https://metacoq.github.io/html MetaCoq \
		--external https://coq-community.org/coq-ext-lib/v0.11.7 ExtLib \
		-R theories/custodian ConCert.x4c.Custodian \
		-R theories/fa2 ConCert.x4c.FA2 \
		-d docs `find . -type f \( -wholename "*theories/*" \) -name "*.v" ! -wholename "./FinCert-ConCert-fork/*" ! -wholename "./_opam/*"`
	cp FinCert-ConCert-fork/extra/resources/coqdocjs/*.js docs
	cp FinCert-ConCert-fork/extra/resources/coqdocjs/*.css docs
	cp FinCert-ConCert-fork/extra/resources/toc/*.js docs
	cp FinCert-ConCert-fork/extra/resources/toc/*.css docs
.PHONY: html
