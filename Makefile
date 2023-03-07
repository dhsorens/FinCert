all: concert theory
.PHONY: all

concert:
	+@make -C phd-thesis-ConCert/utils
	+@make -C phd-thesis-ConCert/execution
.PHONY: concert

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

theory: concert CoqMakefile
	+@make -f CoqMakefile
.PHONY: theory

clean: CoqMakefile
	+@make -f CoqMakefile clean
	+@make -C phd-thesis-ConCert/utils clean
	+@make -C phd-thesis-ConCert/execution clean
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
		--with-header phd-thesis-ConCert/extra/header.html --with-footer phd-thesis-ConCert/extra/footer.html \
		--toc \
		--external https://plv.mpi-sws.org/coqdoc/stdpp stdpp \
		--external https://metacoq.github.io/html MetaCoq \
		--external https://coq-community.org/coq-ext-lib/v0.11.7 ExtLib \
		-R theories/custodian ConCert.x4c.Custodian \
		-R theories/fa2 ConCert.x4c.FA2 \
		-d docs `find . -type f \( -wholename "*theories/*" \) -name "*.v" ! -wholename "./phd-thesis-ConCert/*" ! -wholename "./_opam/*"`
	cp phd-thesis-ConCert/extra/resources/coqdocjs/*.js docs
	cp phd-thesis-ConCert/extra/resources/coqdocjs/*.css docs
	cp phd-thesis-ConCert/extra/resources/toc/*.js docs
	cp phd-thesis-ConCert/extra/resources/toc/*.css docs
.PHONY: html
