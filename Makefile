# make C=theories/topic/conj_name
# compiles the files of a conjecture and those they require (everything without C);
# proof.v is always recompiled when C is given, to print its messages

# make clean C=theories/topic/conj_name
# deletes the compiled files of a conjecture (all generated files without C)

# make check C=theories/topic/conj_name
# checks with rocq-comparator that proof.v proves the statement of main.v without axioms
# (the generated files and the verdict are in _build/check/topic/conj_name)

COMPARATOR ?= rocq-comparator

DIR := $(patsubst %/,%,$(C))
REL := $(patsubst theories/%,%,$(DIR))
MOD := GC.$(subst /,.,$(REL))
OUT := _build/check/$(REL)

.PHONY: build check clean
build:
	@test -z "$(C)" || test -d "$(DIR)" || { echo "no directory $(DIR)"; exit 2; }
	@rocq makefile -f _CoqProject $$(find theories -name '*.v') -o Makefile.coq
	@rm -f $(if $(C),$(DIR)/proof.vo)
	@$(MAKE) --no-print-directory -f Makefile.coq \
	  $(if $(C),$$(find $(DIR) -name '*.v' | sed 's/v$$/vo/'))

check:
	@test -n "$(C)" && test -f "$(DIR)/main.v" && test -f "$(DIR)/proof.v" || \
	  { echo "usage: make check C=theories/topic/conj_name"; exit 2; }
	@mkdir -p $(OUT)
	@rm -f $(OUT)/verdict.json
	@printf 'Require %s.main.\nTheorem statement_holds : %s.main.statement.\nAdmitted.\n' \
	  $(MOD) $(MOD) > $(OUT)/Challenge.v
	@printf 'Require %s.main.\nRequire %s.proof.\nTheorem statement_holds : %s.main.statement.\nProof. exact %s.proof.statement_holds. Qed.\n' \
	  $(MOD) $(MOD) $(MOD) $(MOD) > $(OUT)/Solution.v
	@printf '{ "theorem_names": ["statement_holds"], "permit_challenge_axioms": false, "axiom_policy": "listed" }\n' \
	  > $(OUT)/config.json
	@printf -- '-Q %s/theories GC\n-Q . Check\n' "$(CURDIR)" > $(OUT)/_CoqProject
	@echo "checking $(MOD).main.statement"
	@cd $(OUT) && { $(COMPARATOR) check --pretty config.json > verdict.json; status=$$?; \
	  grep -E '^  "(ok|reason|detail)":' verdict.json; exit $$status; }

clean:
	@test -z "$(C)" || test -d "$(filter theories/%,$(DIR))" || \
	  { echo "usage: make clean [C=theories/topic/conj_name]"; exit 2; }
	@find $(if $(C),$(DIR),theories) -type f \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' \
	  -o -name '*.glob' -o -name '.*.aux' \) -delete
	@rm -rf $(if $(C),$(OUT),_build/check Makefile.coq Makefile.coq.conf .Makefile.coq.d)
