# make C=theories/topic/conj_name
# compiles the files of a conjecture and those they require (everything without C);
# proof.v and implies_*.v are always recompiled when C is given, to print their messages

# make clean C=theories/topic/conj_name
# deletes the compiled files of a conjecture (all generated files without C)

# make check C=theories/topic/conj_name
# checks with rocq-comparator that proof.v proves the proposition conj_name of main.v
# (theorem conj_name_holds) or its negation (theorem conj_name_fails), without axioms
# (a proposition proxy_conj_name is treated in the same way)
# (the generated files and the verdict are in _build/check/topic/conj_name)

# make check C=theories/topic/A B=B
# checks in the same way that implies_B.v proves A -> B (theorem A_implies_B)
# (the generated files and the verdict are in _build/check/topic/A/implies_B)

COMPARATOR ?= rocq-comparator

DIR := $(patsubst %/,%,$(C))
REL := $(patsubst theories/%,%,$(DIR))
NAME := $(notdir $(DIR))
proxy = $(shell grep -qs '^Definition proxy_$(notdir $(1))\>' $(1)/main.v && echo proxy_)$(notdir $(1))
STM = $(call proxy,$(DIR))
MOD := GC.$(subst /,.,$(REL))
FILE := $(if $(B),implies_$(B),proof)
OUT := _build/check/$(REL)$(if $(B),/$(FILE))
# the conjecture B
DIRB := $(if $(B),$(shell find theories -type d -name '$(B)'))
STMB = $(call proxy,$(DIRB))
MODB := GC.$(subst /,.,$(patsubst theories/%,%,$(DIRB)))

.PHONY: build check clean
build:
	@test -z "$(C)" || test -d "$(DIR)" || { echo "no directory $(DIR)"; exit 2; }
	@rocq makefile -f _CoqProject $$(find theories -name '*.v') -o Makefile.coq
	@rm -f $(if $(C),$(DIR)/proof.vo $(DIR)/implies_*.vo)
	@$(MAKE) --no-print-directory -f Makefile.coq \
	  $(if $(C),$$(find $(DIR) -name '*.v' | sed 's/v$$/vo/'))

check:
	@test -n "$(C)" && test -f "$(DIR)/main.v" && test -f "$(DIR)/$(FILE).v" || \
	  { echo "usage: make check C=theories/topic/conj_name [B=other_conj_name]"; exit 2; }
	@test -z "$(B)" || test -f "$(DIRB)/main.v" || { echo "no conjecture $(B)"; exit 2; }
	@mkdir -p $(OUT)
	@rm -f $(OUT)/verdict.json
	@requires='Require $(MOD).main.'; \
	if test -n "$(B)"; \
	then thm=$(STM)_implies_$(STMB); stm='$(MOD).main.$(STM) -> $(MODB).main.$(STMB)'; \
	  requires="$$requires Require $(MODB).main."; \
	elif grep -q '^Theorem $(STM)_fails\>' $(DIR)/proof.v; \
	then thm=$(STM)_fails; stm='~ $(MOD).main.$(STM)'; \
	else thm=$(STM)_holds; stm='$(MOD).main.$(STM)'; fi; \
	printf '%s\nTheorem %s : %s.\nAdmitted.\n' \
	  "$$requires" "$$thm" "$$stm" > $(OUT)/Challenge.v; \
	printf '%s\nRequire %s.%s.\nTheorem %s : %s.\nProof. exact %s.%s.%s. Qed.\n' \
	  "$$requires" "$(MOD)" "$(FILE)" "$$thm" "$$stm" "$(MOD)" "$(FILE)" "$$thm" > $(OUT)/Solution.v; \
	printf '{ "theorem_names": ["%s"], "permit_challenge_axioms": false, "axiom_policy": "listed" }\n' \
	  "$$thm" > $(OUT)/config.json; \
	echo "checking $$thm : $$stm"
	@printf -- '-Q %s/theories GC\n-Q . Check\n' "$(CURDIR)" > $(OUT)/_CoqProject
	@cd $(OUT) && { $(COMPARATOR) check --pretty config.json > verdict.json; status=$$?; \
	  grep -E '^  "(ok|reason|detail)":' verdict.json; exit $$status; }

clean:
	@test -z "$(C)" || test -d "$(filter theories/%,$(DIR))" || \
	  { echo "usage: make clean [C=theories/topic/conj_name]"; exit 2; }
	@find $(if $(C),$(DIR),theories) -type f \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' \
	  -o -name '*.glob' -o -name '.*.aux' \) -delete
	@rm -rf $(if $(C),$(OUT),_build/check Makefile.coq Makefile.coq.conf .Makefile.coq.d)
