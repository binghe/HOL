
####[ Check Software ]################################################

ifeq ($(filter else-if,$(.FEATURES)),)
$(error GNU Make 3.81 needed. Please, update your software.)
	exit 1
endif

# Some people want to call our Makefile snippet with
# make -f LaTeX.mk
# This should not work as $(MAKE) is call recursively and will not read
# LaTeX.mk again. We cannot just add LaTeX.mk to MAKEFILES as LaTeX.mk
# should be read AFTER a standard Makefile (if any) that can define some
# variables (LU_MASTERS, ...) that LaTeX.mk must see.
# So I introduce an HACK here that try to workaround the situation. Keep in
# mind that this hack is not perfect and does not handle all cases
# (for example, "make -f my_latex_config.mk -f LaTeX.mk" will not recurse
# correctly)
ifeq ($(foreach m,$(MAKEFILES), $(m)) $(lastword $(MAKEFILE_LIST)),$(MAKEFILE_LIST))
# We are the first file read after the ones from MAKEFILES
# So we assume we are read due to "-f LaTeX.mk"
LU_LaTeX.mk_NAME := $(lastword $(MAKEFILE_LIST))
# Is this Makefile correctly read for recursive calls ?
ifeq ($(findstring -f $(LU_LaTeX.mk_NAME),$(MAKE)),)
$(info ********************************************************************************)
$(info Warning: $(LU_LaTeX.mk_NAME) called directly. I suppose that you run:)
$(info Warning: $(MAKE) -f $(LU_LaTeX.mk_NAME) $(MAKECMDGOALS))
$(info Warning: or something similar that does not allow recursive invocation of make)
$(info Warning: )
$(info Warning: Trying to enable a workaround. This ACK will be disabled in a future)
$(info Warning: release. Consider using another syntax, for example:)
$(info Warning: $(MAKE) -f $(LU_LaTeX.mk_NAME) MAKE="$(MAKE) -f $(LU_LaTeX.mk_NAME)" $(MAKECMDGOALS))
$(info ********************************************************************************)
MAKE+= -f $(LU_LaTeX.mk_NAME)
endif
endif

####[ Configuration ]################################################

# list of messages categories to display
LU_SHOW ?= warning #info debug debug-vars

# Select GNU/BSD/MACOSX utils (cp, rm, mv, ...)
LU_UTILS ?= $(shell ( /bin/cp --heelp > /dev/null 2>&1 && echo GNU ) || echo BSD )
export LU_UTILS

####[ End of configuration ]################################################
# Modifying the remaining of this document may endanger you life!!! ;)

#---------------------------------------------------------------------
# Controling verbosity
ifdef VERB
MAK_VERB :=  $(VERB)
else
#MAK_VERB :=  debug
#MAK_VERB :=  verbose
#MAK_VERB :=  normal
MAK_VERB :=  quiet
#MAK_VERB :=  silent
endif

#---------------------------------------------------------------------
# MAK_VERB -> verbosity
ifeq ($(MAK_VERB),debug)
COMMON_PREFIX  =  echo "         ======> building " $@ "<======" ; \
	printf "%s $(@F) due to:$(foreach file,$?,\n      * $(file))\n" $1; set -x;
#
COMMON_HIDE   := set -x;
COMMON_CLEAN  := set -x;
SHOW_LATEX:=true
else
ifeq ($(MAK_VERB),verbose)
COMMON_PREFIX  =  echo "         ======> building " $@ "<======" ; \
	printf "%s $(@F) due to:$(foreach file,$?,\n      * $(file))\n" $1;
#
COMMON_HIDE   :=#
COMMON_CLEAN  :=#
SHOW_LATEX:=true
else
ifeq ($(MAK_VERB),normal)
COMMON_PREFIX  =#
COMMON_HIDE   :=  @
COMMON_CLEAN  :=#
SHOW_LATEX:=true
else
ifeq ($(MAK_VERB),quiet)
COMMON_PREFIX  =  @ echo "         ======> building " $@ "<======" ;
#		echo "due to $?" ;
COMMON_HIDE   :=  @
COMMON_CLEAN  :=#
SHOW_LATEX:=
else  # silent
COMMON_PREFIX  =  @
COMMON_HIDE   :=  @
COMMON_CLEAN  :=  @
SHOW_LATEX:=
endif
endif
endif
endif

#---------------------------------------------------------------------
# Old LaTeX have limitations
_LU_PDFTEX_EXT ?= pdftex

#########################################################################
# Utilities
LU_CP=$(LU_CP_$(LU_UTILS))
LU_MV=$(LU_MV_$(LU_UTILS))
LU_RM=$(LU_RM_$(LU_UTILS))
LU_CP_GNU ?= cp -a --
LU_MV_GNU ?= mv --
LU_RM_GNU ?= rm -f --
LU_CP_BSD ?= cp -p
LU_MV_BSD ?= mv
LU_RM_BSD ?= rm -f
LU_CP_MACOSX ?= /bin/cp -p
LU_MV_MACOSX ?= /bin/mv
LU_RM_MACOSX ?= /bin/rm -f

lu-show=\
$(if $(filter $(LU_SHOW),$(1)), \
	$(if $(2), \
		$(if $(filter-out $(2),$(MAKELEVEL)),,$(3)), \
		$(3)))
lu-show-infos=\
$(if $(filter $(LU_SHOW),$(1)), \
	$(if $(2), \
		$(if $(filter-out $(2),$(MAKELEVEL)),,$(warning $(3))), \
		$(warning $(3))))
lu-show-rules=$(call lu-show-infos,info,0,$(1))
lu-show-flavors=$(call lu-show-infos,info,0,$(1))
lu-show-var=$(call lu-show-infos,debug-vars,,  * Set $(1)=$($(1)))
lu-show-read-var=$(eval $(call lu-show-infos,debug-vars,,  Reading $(1) in $(2) ctx: $(3)))$(3)
lu-show-readone-var=$(eval $(call lu-show-infos,debug-vars,,  Reading $(1) for $(2) [one value]: $(3)))$(3)
lu-show-set-var=$(call lu-show-infos,debug-vars,,  * Setting $(1) for $(2) to value: $(3))
lu-show-add-var=$(call lu-show-infos,debug-vars,,  * Adding to $(1) for $(2) values: $(value 3))
lu-show-add-var2=$(call lu-show-infos,warning,,  * Adding to $(1) for $(2) values: $(value 3))

lu-save-file=$(call lu-show,debug,,echo "saving $1" ;) \
	if [ -f "$1" ];then $(LU_CP) "$1" "$2" ;else $(LU_RM) "$2" ;fi
lu-cmprestaure-file=\
	if cmp -s "$1" "$2"; then \
		$(LU_MV) "$2" "$1" ; \
		$(call lu-show,debug,,echo "$1" not modified ;) \
	else \
		$(call lu-show,debug,,echo "$1" modified ;) \
		if [ -f "$2" -o -f "$1" ]; then \
			$(RM) -- "$2" ; \
			$3 \
		fi ; \
	fi

lu-clean=$(if $(strip $(1)),$(RM) $(1))

define lu-bug # description
  $$(warning Internal error: $(1))
  $$(error You probably found a bug. Please, report it.)
endef

#########################################################################
#########################################################################
#########################################################################
#########################################################################
##################                              #########################
##################          Variables           #########################
##################                              #########################
#########################################################################
#########################################################################
#########################################################################
#########################################################################
#########################################################################
#
# _LU_FLAVORS_DEFINED : list of available flavors
# _LU_FLAV_*_'flavname' : per flavor variables
#   where * can be :
#   PROGNAME : variable name for programme (and .._OPTIONS for options)
#   EXT : extension of created file
#   TARGETNAME : global target
#   DEPFLAVOR : flavor to depend upon
#   CLEANFIGEXT : extensions to clean for fig figures
_LU_FLAVORS_DEFINED = $(_LU_FLAVORS_DEFINED_TEX) $(_LU_FLAVORS_DEFINED_DVI)

# INDEXES_TYPES = GLOSS INDEX
# INDEXES_INDEX = name1 ...
# INDEXES_GLOSS = name2 ...
# INDEX_name1_SRC
# GLOSS_name2_SRC

define _lu-getvalues# 1:VAR 2:CTX (no inheritage)
$(if $(filter-out undefined,$(origin LU_$2$1)),$(LU_$2$1),$($2$1) $(_LU_$2$1_MK) $(TD_$2$1))
endef
define lu-define-addvar # 1:suffix_fnname 2:CTX 3:disp-debug 4:nb_args 5:inherited_ctx 6:ctx-build-depend
  define lu-addtovar$1 # 1:VAR 2:... $4: value
    _LU_$2$$1_MK+=$$($4)
    $$(call lu-show-add-var,$$1,$3,$$(value $4))
  endef
  define lu-def-addvar-inherited-ctx$1 # 1:VAR 2:...
    $6
    _LU_$2$$1_INHERITED_CTX=$$(sort \
      $$(foreach ctx,$5,$$(ctx) $$(if $$(filter-out undefined,$$(origin \
          LU_$$(ctx)$$1)),,\
         $$(_LU_$$(ctx)$$1_INHERITED_CTX))))
    $$$$(call lu-show-var,_LU_$2$$1_INHERITED_CTX)
  endef
  define lu-getvalues$1# 1:VAR 2:...
$$(if $$(filter-out undefined,$$(origin _LU_$2$$1_INHERITED_CTX)),,$$(eval \
  $$(call lu-def-addvar-inherited-ctx$1,$$1,$$2,$$3,$$4,$$5,$$6)\
))$$(call lu-show-read-var,$$1,$3,$$(foreach ctx,\
    $(if $2,$2,GLOBAL) $$(if $$(filter-out undefined,$$(origin LU_$2$$1)),,\
             $$(_LU_$2$$1_INHERITED_CTX))\
    ,$$(call _lu-getvalues,$$1,$$(filter-out GLOBAL,$$(ctx)))))
  endef
endef

# Global variable
# VAR (DEPENDS)
$(eval $(call lu-define-addvar,-global,,global,2))

# Per flavor variable
# FLAVOR_$2_VAR (FLAVOR_DVI_DEPENDS)
# 2: flavor name
# Inherit from VAR (DEPENDS)
$(eval $(call lu-define-addvar,-flavor,FLAVOR_$$2_,flavor $$2,3,\
  GLOBAL,\
  $$(eval $$(call lu-def-addvar-inherited-ctx-global,$$1)) \
))

# Per master variable
# $2_VAR (source_DEPENDS)
# 2: master name
# Inherit from VAR (DEPENDS)
$(eval $(call lu-define-addvar,-master,$$2_,master $$2,3,\
  GLOBAL,\
  $$(eval $$(call lu-def-addvar-inherited-ctx-global,$$1)) \
))

# Per target variable
# $2$(EXT of $3)_VAR (source.dvi_DEPENDS)
# 2: master name
# 3: flavor name
# Inherit from $2_VAR FLAVOR_$3_VAR (source_DEPENDS FLAVOR_DVI_DEPENDS)
$(eval $(call lu-define-addvar,,$$2$$(call lu-getvalue-flavor,EXT,$$3)_,target $$2$$(call lu-getvalue-flavor,EXT,$$3),4,\
  $$2_ FLAVOR_$$3_,\
  $$(eval $$(call lu-def-addvar-inherited-ctx-master,$$1,$$2)) \
  $$(eval $$(call lu-def-addvar-inherited-ctx-flavor,$$1,$$3)) \
))

# Per index/glossary variable
# $(2)_$(3)_VAR (INDEX_source_DEPENDS)
# 2: type (INDEX, GLOSS, ...)
# 3: index name
# Inherit from VAR (DEPENDS)
$(eval $(call lu-define-addvar,-global-index,$$2_$$3_,index $$3[$$2],4,\
  GLOBAL,\
  $$(eval $$(call lu-def-addvar-inherited-ctx-global,$$1)) \
))

# Per master and per index/glossary variable
# $(2)_$(3)_$(4)_VAR (source_INDEX_source_DEPENDS)
# 2: master name
# 3: type (INDEX, GLOSS, ...)
# 4: index name
# Inherit from $2_VAR $3_$4_VAR (source_DEPENDS INDEX_source_DEPENDS)
$(eval $(call lu-define-addvar,-master-index,$$2_$$3_$$4_,index $$2/$$4[$$3],5,\
  $$2_ $$3_$$4_,\
  $$(eval $$(call lu-def-addvar-inherited-ctx-master,$$1,$$2)) \
  $$(eval $$(call lu-def-addvar-inherited-ctx-global-index,$$1,$$3,$$4)) \
))

# Per target and per index/glossary variable
# $(2)$(EXT of $3)_$(4)_$(5)_VAR (source.dvi_INDEX_source_DEPENDS)
# 2: master name
# 3: flavor name
# 4: type (INDEX, GLOSS, ...)
# 5: index name
# Inherit from $2$(EXT of $3)_VAR $(2)_$(3)_$(4)_VAR
# (source.dvi_DEPENDS source_INDEX_source_DEPENDS)
$(eval $(call lu-define-addvar,-index,$$2$$(call lu-getvalue-flavor,EXT,$$3)_$$4_$$5_,index $$2$$(call lu-getvalue-flavor,EXT,$$3)/$$5[$$4],6,\
  $$2$$(call lu-getvalue-flavor,EXT,$$3)_ $$2_$$4_$$5_,\
  $$(eval $$(call lu-def-addvar-inherited-ctx,$$1,$$2,$$3)) \
  $$(eval $$(call lu-def-addvar-inherited-ctx-master-index,$$1,$$2,$$4,$$5)) \
))

define lu-setvar-global # 1:name 2:value
  _LU_$(1) ?= $(2)
  $$(eval $$(call lu-show-set-var,$(1),global,$(2)))
endef

define lu-setvar-flavor # 1:name 2:flavor 3:value
  _LU_FLAVOR_$(2)_$(1) ?= $(3)
  $$(eval $$(call lu-show-set-var,$(1),flavor $(2),$(3)))
endef

define lu-setvar-master # 1:name 2:master 3:value
  _LU_$(2)_$(1) ?= $(3)
  $$(eval $$(call lu-show-set-var,$(1),master $(2),$(3)))
endef

define lu-setvar # 1:name 2:master 3:flavor 4:value
  _LU_$(2)$$(call lu-getvalue-flavor,EXT,$(3))_$(1)=$(4)
  $$(eval $$(call lu-show-set-var,$(1),master/flavor $(2)/$(3),$(4)))
endef

define lu-getvalue # 1:name 2:master 3:flavor
$(call lu-show-readone-var,$(1),master/flavor $(2)/$(3),$(or \
	$(LU_$(2)$(call lu-getvalue-flavor,EXT,$(3))_$(1)), \
	$(TD_$(2)$(call lu-getvalue-flavor,EXT,$(3))_$(1)), \
	$(LU_$(2)_$(1)), \
	$($(2)_$(1)), \
	$(LU_FLAVOR_$(3)_$(1)), \
	$(LU_$(1)), \
	$($(1)), \
	$(_LU_$(2)$(call lu-getvalue-flavor,EXT,$(3))_$(1)), \
	$(_LU_$(2)_$(1)), \
	$(_LU_FLAVOR_$(3)_$(1)), \
	$(_LU_$(1))\
))
endef

define lu-getvalue-flavor # 1:name 2:flavor
$(call lu-show-readone-var,$(1),flavor $(2),$(or \
	$(LU_FLAVOR_$(2)_$(1)), \
	$(LU_$(1)), \
	$($(1)), \
	$(_LU_FLAVOR_$(2)_$(1)), \
	$(_LU_$(1))\
))
endef

define lu-getvalue-master # 1:name 2:master
$(call lu-show-readone-var,$(1),master $(2),$(or \
	$(LU_$(2)_$(1)), \
	$($(2)_$(1)), \
	$(LU_$(1)), \
	$($(1)), \
	$(_LU_$(2)_$(1)), \
	$(_LU_$(1))\
))
endef

define lu-getvalue-index # 1:name 2:master 3:flavor 4:type 5:indexname
$(call lu-show-readone-var,$(1),master/flavor/index $(2)/$(3)/[$(4)]$(5),$(or \
	$(LU_$(2)$(call lu-getvalue-flavor,EXT,$(3))_$(4)_$(5)_$(1)), \
	$(LU_$(2)_$(4)_$(5)_$(1)), \
	$(TD_$(2)$(call lu-getvalue-flavor,EXT,$(3))_$(4)_$(5)_$(1)), \
	$($(2)_$(4)_$(5)_$(1)), \
	$(LU_$(4)_$(5)_$(1)), \
	$($(4)_$(5)_$(1)), \
	$(LU_$(2)$(call lu-getvalue-flavor,EXT,$(3))_$(4)_$(1)), \
	$(LU_$(2)_$(4)_$(1)), \
	$($(2)_$(4)_$(1)), \
	$(LU_$(4)_$(1)), \
	$($(4)_$(1)), \
	$(LU_$(2)_$(1)), \
	$($(2)_$(1)), \
	$(LU_FLAVOR_$(3)_$(1)), \
	$(LU_$(1)), \
	$($(1)), \
	$(_LU_$(2)$(call lu-getvalue-flavor,EXT,$(3))_$(4)_$(5)_$(1)), \
	$(_LU_$(2)_$(4)_$(5)_$(1)), \
	$(_LU_$(4)_$(5)_$(1)), \
	$(_LU_$(2)$(call lu-getvalue-flavor,EXT,$(3))_$(4)_$(1)), \
	$(_LU_$(2)_$(4)_$(1)), \
	$(_LU_FLAVOR_$(3)_$(4)_$(1)), \
	$(_LU_$(4)_$(1)), \
	$(_LU_$(2)$(call lu-getvalue-flavor,EXT,$(3))_$(1)), \
	$(_LU_$(2)_$(1)), \
	$(_LU_FLAVOR_$(3)_$(1)), \
	$(_LU_$(1))\
))
endef

define lu-call-prog # 1:varname 2:master 3:flavor [4:index]
$(call lu-getvalue,$(1),$(2),$(3)) $(call lu-getvalues,$(1)_OPTIONS,$(2),$(3))
endef

define lu-call-prog-index # 1:varname 2:master 3:flavor 4:type 5:indexname
$(call lu-getvalue$(if $(4),-index),$(1),$(2),$(3),$(4),$(5)) \
	$(call lu-getvalues$(if $(4),-index),$(1)_OPTIONS,$(2),$(3),$(4),$(5))
endef

define lu-call-prog-flavor # 1:master 2:flavor
$(call lu-call-prog,$(call lu-getvalue,VARPROG,$(1),$(2)),$(1),$(2))
endef

#########################################################################
#########################################################################
#########################################################################
#########################################################################
##################                              #########################
##################     Global variables         #########################
##################                              #########################
#########################################################################
#########################################################################
#########################################################################
#########################################################################
#########################################################################

# Globals variables
$(eval $(call lu-setvar-global,LATEX,latex))
$(eval $(call lu-setvar-global,PDFLATEX,pdflatex))
$(eval $(call lu-setvar-global,LUALATEX,lualatex))
$(eval $(call lu-setvar-global,DVIPS,dvips))
$(eval $(call lu-setvar-global,DVIPDFM,dvipdfm))
$(eval $(call lu-setvar-global,BIBTEX,bibtex))
#$(eval $(call lu-setvar-global,MPOST,TEX="$(LATEX)" mpost))
$(eval $(call lu-setvar-global,FIG2DEV,fig2dev))
#$(eval $(call lu-setvar-global,SVG2DEV,svg2dev))
$(eval $(call lu-setvar-global,EPSTOPDF,epstopdf))
$(eval $(call lu-setvar-global,MAKEINDEX,makeindex))

# workaround the fact that $(shell ...) ignore locally exported variables
# get only the variables with plain names
_LU_MAKE_ENV := $(shell echo '$(.VARIABLES)' | awk -v RS=' ' '/^[a-zA-Z0-9]+$$/')
_LU_SHELL_EXPORT := $(foreach v,$(_LU_MAKE_ENV),$(v)='$($(v))')
_lu_run_kpsewhich=$(shell $(_LU_SHELL_EXPORT) kpsewhich -format $1 $2)

# Look first into the TDS (texmfscripts), then in PATH for our program
# At each location, we prefer with suffix than without
define _lu_which # VARNAME progname
 ifeq ($(origin _LU_$(1)_DEFAULT), undefined)
 _LU_$(1)_DEFAULT := $$(firstword $$(wildcard \
	$$(call _lu_run_kpsewhich,texmfscripts,$(2)) \
	$$(call _lu_run_kpsewhich,texmfscripts,$$(basename $(2))) \
	$$(foreach dir,$$(subst :, ,$$(PATH)), \
		$$(dir)/$(2) $$(dir)/$$(basename $(2))) \
	) $(2))
 export _LU_$(1)_DEFAULT
 _LU_$(1)_DEFAULT_OLD := $$(firstword $$(wildcard \
     $$(addprefix bin/,$(2) $$(basename $(2))) \
     $$(addprefix ./,$(2) $$(basename $(2)))))
 $$(if $$(filter-out $$(_LU_$(1)_DEFAULT), $$(_LU_$(1)_DEFAULT_OLD)),\
   $$(if $$(_lu_scripts_warnings),, \
     $$(eval _lu_scripts_warnings:=done) \
     $$(warning By default, this version of LaTeX-Make do not use \
     scripts in $$(dir $$(_LU_$(1)_DEFAULT_OLD)) anymore.) \
     $$(warning For example $$(_LU_$(1)_DEFAULT) is used instead of $$(_LU_$(1)_DEFAULT_OLD))\
     $$(warning If you want to keep the old behavior, add into your \
     Makefile something like:)\
     $$(warning export TEXMFSCRIPTS:=$$(dir $$(_LU_$(1)_DEFAULT_OLD))$$$$(addprefix :,$$$$(TEXMFSCRIPTS))::)))
 #$$(warning _LU_$(1)_DEFAULT=$$(_LU_$(1)_DEFAULT))
 endif
 $$(eval $$(call lu-setvar-global,$(1),$$(_LU_$(1)_DEFAULT)))
endef

$(eval $(call _lu_which,GENSUBFIG,gensubfig.py))
$(eval $(call _lu_which,FIGDEPTH,figdepth.py))
$(eval $(call _lu_which,GENSUBSVG,gensubfig.py))
$(eval $(call _lu_which,SVGDEPTH,svgdepth.py))
$(eval $(call _lu_which,SVG2DEV,svg2dev.py))
$(eval $(call _lu_which,LATEXFILTER,latexfilter.py))

# Rules to use to check if the build document (dvi or pdf) is up-to-date
# This can be overruled per document manually and/or automatically
#REBUILD_RULES ?= latex texdepends bibtopic bibtopic_undefined_references
$(eval $(call lu-addtovar-global,REBUILD_RULES,latex texdepends))

# Default maximum recursion level
$(eval $(call lu-setvar-global,MAX_REC,6))

#########################################################################
#########################################################################
#########################################################################
#########################################################################
##################                              #########################
##################          Flavors             #########################
##################                              #########################
#########################################################################
#########################################################################
#########################################################################
#########################################################################
#########################################################################

define lu-create-texflavor # 1:name 2:tex_prog 3:file_ext
			   # 4:master_cible 5:fig_extention_to_clean
  _LU_FLAVORS_DEFINED_TEX += $(1)
  $(eval $(call lu-setvar-flavor,VARPROG,$(1),$(2)))
  $(eval $(call lu-setvar-flavor,EXT,$(1),$(3)))
  $(eval $(call lu-setvar-flavor,TARGETNAME,$(1),$(4)))
  $(eval $(call lu-addtovar-flavor,CLEANFIGEXT,$(1),$(5)))
  $(eval $(call lu-addtovar-flavor,CLEANSVGEXT,$(1),$(5)))
endef

define lu-create-dviflavor # 1:name 2:dvi_prog 3:file_ext
			   # 4:master_cible 5:tex_flavor_depend
  $$(eval $$(call lu-define-flavor,$(5)))
  _LU_FLAVORS_DEFINED_DVI += $(1)
  $(eval $(call lu-setvar-flavor,VARPROG,$(1),$(2)))
  $(eval $(call lu-setvar-flavor,EXT,$(1),$(3)))
  $(eval $(call lu-setvar-flavor,TARGETNAME,$(1),$(4)))
  $(eval $(call lu-setvar-flavor,DEPFLAVOR,$(1),$(5)))
endef

define lu-create-flavor # 1:name 2:type 3..7:options
  $$(if $$(filter $(1),$(_LU_FLAVORS_DEFINED)), \
	$$(call lu-show-flavors,Flavor $(1) already defined), \
	$$(call lu-show-flavors,Creating flavor $(1) ($(2))) \
	$$(eval $$(call lu-create-$(2)flavor,$(1),$(3),$(4),$(5),$(6),$(7))))
endef

define lu-define-flavor # 1:name
  $$(eval $$(call lu-define-flavor-$(1)))
endef

define lu-flavor-rules # 1:name
 $$(call lu-show-flavors,Defining rules for flavor $(1))
 $$(if $$(call lu-getvalue-flavor,TARGETNAME,$(1)), \
 $$(call lu-getvalue-flavor,TARGETNAME,$(1)): \
	$$(call lu-getvalues-flavor,TARGETS,$(1)))
 $$(if $$(call lu-getvalue-flavor,TARGETNAME,$(1)), \
 .PHONY: $$(call lu-getvalue-flavor,TARGETNAME,$(1)))
endef

define lu-define-flavor-DVI #
  $$(eval $$(call lu-create-flavor,DVI,tex,LATEX,.dvi,dvi,\
	.pstex_t .pstex))
endef

define lu-define-flavor-PDF #
  $$(eval $$(call lu-create-flavor,PDF,tex,PDFLATEX,.pdf,pdf,\
	.pdftex_t .$$(_LU_PDFTEX_EXT)))
endef

define lu-define-flavor-LUALATEX #
  $$(eval $$(call lu-create-flavor,LUALATEX,tex,LUALATEX,.pdf,pdf,\
	.pdftex_t .$$(_LU_PDFTEX_EXT)))
endef

define lu-define-flavor-PS #
  $$(eval $$(call lu-create-flavor,PS,dvi,DVIPS,.ps,ps,DVI))
endef

define lu-define-flavor-DVIPDF #
  $$(eval $$(call lu-create-flavor,DVIPDF,dvi,DVIPDFM,.pdf,pdf,DVI))
endef

$(eval $(call lu-addtovar-global,FLAVORS,PDF PS))

#########################################################################
#########################################################################
#########################################################################
#########################################################################
##################                              #########################
##################          Masters             #########################
##################                              #########################
#########################################################################
#########################################################################
#########################################################################
#########################################################################
#########################################################################

define _lu-do-latex # 1:master 2:flavor 3:source.tex 4:ext(.dvi/.pdf)
  exec 3>&1; \
  run() { \
	printf "Running:" 1>&3 ; \
	for arg; do \
		printf "%s" " '$$arg'" 1>&3 ; \
	done ; echo 1>&3 ; \
	"$$@" ; \
  }; \
  doit() { \
	$(RM) -v "$(1)$(4)_FAILED"  \
		"$(1)$(4)_NEED_REBUILD" \
		"$(1)$(4).mk" ;\
		( 	echo X | \
			run $(call lu-call-prog-flavor,$(1),$(2)) \
				--interaction errorstopmode \
				--jobname "$(1)" \
	'\RequirePackage[extension='"$(4)"']{texdepends}\input'"{$(3)}" || \
			touch "$(1)$(4)_FAILED" ; \
			if grep -sq '^! LaTeX Error:' "$(1).log" ; then \
				touch "$(1)$(4)_FAILED" ; \
			fi \
		) | $(call lu-call-prog,LATEXFILTER,$(1),$(2)) ; \
	NO_TEXDEPENDS_FILE=0 ;\
	if [ ! -f "$(1)$(4).mk" ]; then \
		NO_TEXDEPENDS_FILE=1 ;\
	fi ;\
	sed -e 's,\\openout[0-9]* = \([^`].*\),TD_$(1)$(4)_OUTPUTS += \1,p;s,\\openout[0-9]* = `\(.*\)'"'.,TD_$(1)$(4)_OUTPUTS += \1,p;d" \
		"$(1).log" >> "$(1)$(4).mk" ;\
	if [ -f "$(1)$(4)_FAILED" ]; then \
		echo "*************************************" ;\
		echo "Building $(1)$(4) fails" ;\
		echo "*************************************" ;\
		echo "Here are the last lines of the log file" ;\
		echo "If this is not enought, try to" ;\
		echo "call 'make' with 'VERB=verbose' option" ;\
		echo "*************************************" ;\
		echo "==> Last lines in $(1).log <==" ; \
		sed -e '/^[?] X$$/,$$d' \
		    -e '/^Here is how much of TeX'"'"'s memory you used:$$/,$$d' \
			< "$(1).log" | tail -n 20; \
		return 1; \
	fi; \
	if [ "$$NO_TEXDEPENDS_FILE" = 1 ]; then \
		echo "*************************************" ;\
		echo "texdepends does not seems be loaded" ;\
		echo "Either your (La)TeX installation is wrong or you found a bug." ;\
		echo "If so, please, report it (with the result of shell command 'kpsepath tex')";\
		echo "Aborting compilation" ;\
		echo "*************************************" ;\
		touch "$(1)$(4)_FAILED" ; \
		return 1 ;\
	fi ;\
    }; doit
endef

.PHONY: clean-build-fig

##########################################################
define lu-master-texflavor-index-vars # MASTER FLAVOR TYPE INDEX ext(.dvi/.pdf)
 $$(call lu-show-rules,Setting flavor index vars for $(1)/$(2)/[$(3)]$(4))
 $$(eval $$(call lu-addtovar,DEPENDS,$(1),$(2), \
    $$(call lu-getvalue-index,TARGET,$(1),$(2),$(3),$(4))))
 $$(eval $$(call lu-addtovar,WATCHFILES,$(1),$(2), \
    $$(call lu-getvalue-index,SRC,$(1),$(2),$(3),$(4))))
endef ####################################################
define lu-master-texflavor-index-rules # MASTER FLAVOR TYPE INDEX ext(.dvi/.pdf)
 $$(call lu-show-rules,Setting flavor index rules for $(1)/$(2)/[$(3)]$(4))
 $$(if $$(_LU_DEF_IND_$$(call lu-getvalue-index,TARGET,$(1),$(2),$(3),$(4))), \
   $$(call lu-show-rules,=> Skipping: already defined in flavor $$(_LU_DEF_IND_$$(call lu-getvalue-index,TARGET,$(1),$(2),$(3),$(4)))), \
   $$(eval $$(call _lu-master-texflavor-index-rules\
	,$(1),$(2),$(3),$(4),$(5),$$(call lu-getvalue-index,TARGET,$(1),$(2),$(3),$(4)))))
endef
define _lu-master-texflavor-index-rules # MASTER FLAVOR TYPE INDEX ext TARGET
 $(6): \
    $$(call lu-getvalue-index,SRC,$(1),$(2),$(3),$(4)) \
    $$(wildcard $$(call lu-getvalue-index,STYLE,$(1),$(2),$(3),$(4)))
	$$(COMMON_PREFIX)$$(call lu-call-prog-index,MAKEINDEX,$(1),$(2),$(3),$(4)) \
	  $$(addprefix -s ,$$(call lu-getvalue-index,STYLE,$(1),$(2),$(3),$(4))) \
	  -o $$@ $$<
 _LU_DEF_IND_$(6)=$(2)
 clean::
	$$(call lu-clean,$$(call lu-getvalue-index,TARGET,$(1),$(2),$(3),$(4)) \
		$$(addsuffix .ilg,$$(basename \
			$$(call lu-getvalue-index,SRC,$(1),$(2),$(3),$(4)))))
endef ####################################################
define lu-master-texflavor-index # MASTER FLAVOR INDEX ext(.dvi/.pdf)
 $$(eval $$(call lu-master-texflavor-index-vars,$(1),$(2),$(3),$(4)))
 $$(eval $$(call lu-master-texflavor-index-rules,$(1),$(2),$(3),$(4)))
endef
##########################################################

##########################################################
define lu-master-texflavor-vars # MASTER FLAVOR ext(.dvi/.pdf)
 $$(call lu-show-rules,Setting flavor vars for $(1)/$(2))
 -include $(1)$(3).mk
 $$(eval $$(call lu-addtovar,DEPENDS,$(1),$(2), \
               $$(call lu-getvalues,FIGURES,$(1),$(2)) \
               $$(call lu-getvalues,BIBFILES,$(1),$(2)) \
   $$(wildcard $$(call lu-getvalues,INPUTS,$(1),$(2))) \
   $$(wildcard $$(call lu-getvalues,BIBSTYLES,$(1),$(2))) \
               $$(call lu-getvalues,BBLFILES,$(1),$(2))\
 ))

 $$(eval $$(call lu-addtovar-flavor,TARGETS,$(2),$(1)$(3)))

 $$(eval $$(call lu-addtovar,GPATH,$(1),$(2), \
     $$(subst },,$$(subst {,,$$(subst }{, ,\
	$$(call lu-getvalue,GRAPHICSPATH,$(1),$(2)))))))

 $$(if $$(sort $$(call lu-getvalues,SUBFIGS,$(1),$(2))), \
	$$(eval include $$(addsuffix .mk,$$(sort \
		$$(call lu-getvalues,SUBFIGS,$(1),$(2))))))

 $$(eval $$(call lu-addtovar,WATCHFILES,$(1),$(2), \
	$$(filter %.aux, $$(call lu-getvalues,OUTPUTS,$(1),$(2)))))

 $$(foreach type,$$(call lu-getvalues,INDEXES,$(1),$(2)), \
   $$(foreach index,$$(call lu-getvalues,INDEXES_$$(type),$(1),$(2)), \
    $$(eval $$(call lu-master-texflavor-index-vars,$(1),$(2),$$(type),$$(index),$(3)))))
endef ####################################################
define lu-master-texflavor-rules # MASTER FLAVOR ext(.dvi/.pdf)
 $$(call lu-show-rules,Defining flavor rules for $(1)/$(2))
 $$(call lu-getvalues,BBLFILES,$(1),$(2)): \
	$$(sort             $$(call lu-getvalues,BIBFILES,$(1),$(2)) \
		$$(wildcard $$(call lu-getvalues,BIBSTYLES,$(1),$(2))))
 $(1)$(3): %$(3): \
   $$(filter-out $$(call lu-getvalues,DEPENDS_EXCLUDE,$(1),$(2)), \
     $$(call lu-getvalues,DEPENDS,$(1),$(2)) \
     $$(call lu-getvalues,REQUIRED,$(1),$(2))) \
   $$(if $$(wildcard $(1)$(3)_FAILED),LU_FORCE,) \
   $$(if $$(wildcard $(1)$(3)_NEED_REBUILD),LU_FORCE,) \
   $$(if $$(wildcard $(1)$(3)_NEED_REBUILD_IN_PROGRESS),LU_FORCE,)
	$$(if $$(filter-out $$(LU_REC_LEVEL),$$(call lu-getvalue,MAX_REC,$(1),$(2))),, \
		$$(warning *********************************) \
		$$(warning *********************************) \
		$$(warning *********************************) \
		$$(warning Stopping generation of $$@) \
		$$(warning I got max recursion level $$(call lu-getvalue,MAX_REC,$(1),$(2))) \
		$$(warning Set LU_$(1)_$(2)_MAX_REC, LU_MAX_REC_$(1) or LU_MAX_REC if you need it) \
		$$(warning *********************************) \
		$$(warning *********************************) \
		$$(warning *********************************) \
		$$(error Aborting generation of $$@))
	$$(MAKE) LU_REC_MASTER="$(1)" LU_REC_FLAVOR="$(2)" LU_REC_TARGET="$$@"\
		LU_WATCH_FILES_SAVE
	$$(COMMON_PREFIX)$$(call _lu-do-latex\
		,$(1),$(2),$$(call lu-getvalue-master,MAIN,$(1)),$(3))
	$$(MAKE) LU_REC_MASTER="$(1)" LU_REC_FLAVOR="$(2)" LU_REC_TARGET="$$@"\
		LU_WATCH_FILES_RESTORE
	$$(MAKE) LU_REC_MASTER="$(1)" LU_REC_FLAVOR="$(2)" LU_REC_TARGET="$$@"\
		$(1)$(3)_NEED_REBUILD
ifneq ($(LU_REC_TARGET),)
 $(1)$(3)_NEED_REBUILD_IN_PROGRESS:
	$$(COMMON_HIDE)touch $(1)$(3)_NEED_REBUILD_IN_PROGRESS
 $$(addprefix LU_rebuild_,$$(call lu-getvalues,REBUILD_RULES,$(1),$(2))): \
	$(1)$(3)_NEED_REBUILD_IN_PROGRESS
.PHONY: $(1)$(3)_NEED_REBUILD
 $(1)$(3)_NEED_REBUILD: \
    $(1)$(3)_NEED_REBUILD_IN_PROGRESS \
    $$(addprefix LU_rebuild_,$$(call lu-getvalues,REBUILD_RULES,$(1),$(2)))
	$$(COMMON_HIDE)$(RM) $(1)$(3)_NEED_REBUILD_IN_PROGRESS
	$$(COMMON_HIDE)if [ -f "$(1)$(3)_NEED_REBUILD" ];then\
		echo "********************************************" ;\
		echo "*********** New build needed ***************" ;\
		echo "********************************************" ;\
		cat "$(1)$(3)_NEED_REBUILD" ; \
		echo "********************************************" ;\
	fi
	$$(MAKE) LU_REC_LEVEL=$$(shell expr $$(LU_REC_LEVEL) + 1) \
		$$(LU_REC_TARGET)
endif
 clean-build-fig::
	$$(call lu-clean,$$(foreach fig, \
	   $$(basename $$(wildcard $$(filter %.fig, \
			$$(call lu-getvalues,FIGURES,$(1),$(2))))), \
	   $$(addprefix $$(fig),$$(call lu-getvalues-flavor,CLEANFIGEXT,$(2)))))
	$$(call lu-clean,$$(foreach svg, \
	   $$(basename $$(wildcard $$(filter %.svg, \
			$$(call lu-getvalues,FIGURES,$(1),$(2))))), \
	   $$(addprefix $$(svg),$$(call lu-getvalues-flavor,CLEANSVGEXT,$(2)))))
 clean:: clean-build-fig
	$$(call lu-clean,$$(call lu-getvalues,OUTPUTS,$(1),$(2)) \
		$$(call lu-getvalues,BBLFILES,$(1),$(2)) \
		$$(addsuffix .mk,$$(call lu-getvalues,SUBFIGS,$(1),$(2))) \
	    $$(patsubst %.bbl,%.blg,$$(call lu-getvalues,BBLFILES,$(1),$(2))))
	$$(call lu-clean,$$(wildcard $(1).log))
 distclean::
	$$(call lu-clean,$$(wildcard $(1)$(3) $(1)$(3)_FAILED \
		$(1)$(3)_NEED_REBUILD $(1)$(3)_NEED_REBUILD_IN_PROGRESS))
 $$(foreach type,$$(call lu-getvalues,INDEXES,$(1),$(2)), \
   $$(foreach index,$$(call lu-getvalues,INDEXES_$$(type),$(1),$(2)), \
    $$(eval $$(call lu-master-texflavor-index-rules,$(1),$(2),$$(type),$$(index),$(3)))))
endef ####################################################
define lu-master-texflavor # MASTER FLAVOR ext(.dvi/.pdf)
 $$(eval $$(call lu-master-texflavor-vars,$(1),$(2),$(3)))
 $$(eval $$(call lu-master-texflavor-rules,$(1),$(2),$(3)))
endef
##########################################################

##########################################################
define lu-master-dviflavor-vars # MASTER FLAVOR ext(.ps)
 $$(call lu-show-rules,Setting flavor vars for \
	$(1)/$(2)/$$(call lu-getvalue-flavor,DEPFLAVOR,$(2)))
# $$(eval $$(call lu-addvar,VARPROG,$(1),$(2)))
# $$(eval $$(call lu-addvar,$$(call lu-getvalue,VARPROG,$(1),$(2)),$(1),$(2)))
 $$(eval $$(call lu-addtovar-flavor,TARGETS,$(2),$(1)$(3)))
endef ####################################################
define lu-master-dviflavor-rules # MASTER FLAVOR ext(.ps)
 $$(call lu-show-rules,Defining flavor rules for \
	$(1)/$(2)/$$(call lu-getvalue-flavor,DEPFLAVOR,$(2)))
 $(1)$(3): %$(3): %$$(call lu-getvalue-flavor,EXT,$$(call lu-getvalue-flavor,DEPFLAVOR,$(2)))
	$$(call lu-call-prog-flavor,$(1),$(2))	-o $$@ $$<
 distclean::
	$$(call lu-clean,$$(wildcard $(1)$(3)))
endef ####################################################
define lu-master-dviflavor # MASTER FLAVOR ext(.ps)
 $$(eval $$(call lu-master-dviflavor-vars,$(1),$(2),$(3)))
 $$(eval $$(call lu-master-dviflavor-rules,$(1),$(2),$(3)))
endef
##########################################################

##########################################################
define lu-master-vars # MASTER
 $$(call lu-show-rules,Setting vars for $(1))
 $$(eval $$(call lu-setvar-master,MAIN,$(1),$(1).tex))
 $$(eval $$(call lu-addtovar-master,DEPENDS,$(1),\
	$$(call lu-getvalue-master,MAIN,$(1))))
 _LU_$(1)_DVI_FLAVORS=$$(filter $$(_LU_FLAVORS_DEFINED_DVI),\
	$$(sort $$(call lu-getvalues-master,FLAVORS,$(1))))
 _LU_$(1)_TEX_FLAVORS=$$(filter $$(_LU_FLAVORS_DEFINED_TEX),\
	$$(sort $$(call lu-getvalues-master,FLAVORS,$(1)) \
		$$(LU_REC_FLAVOR) \
	$$(foreach dvi,$$(call lu-getvalues-master,FLAVORS,$(1)), \
		$$(call lu-getvalue-flavor,DEPFLAVOR,$$(dvi)))))
 $$(foreach flav,$$(_LU_$(1)_TEX_FLAVORS), $$(eval $$(call \
	lu-master-texflavor-vars,$(1),$$(flav),$$(call lu-getvalue-flavor,EXT,$$(flav)))))
 $$(foreach flav,$$(_LU_$(1)_DVI_FLAVORS), $$(eval $$(call \
	lu-master-dviflavor-vars,$(1),$$(flav),$$(call lu-getvalue-flavor,EXT,$$(flav)))))
endef ####################################################
define lu-master-rules # MASTER
 $$(call lu-show-rules,Defining rules for $(1))
 $$(foreach flav,$$(_LU_$(1)_TEX_FLAVORS), $$(eval $$(call \
	lu-master-texflavor-rules,$(1),$$(flav),$$(call lu-getvalue-flavor,EXT,$$(flav)))))
 $$(foreach flav,$$(_LU_$(1)_DVI_FLAVORS), $$(eval $$(call \
	lu-master-dviflavor-rules,$(1),$$(flav),$$(call lu-getvalue-flavor,EXT,$$(flav)))))
endef ####################################################
define lu-master # MASTER
 $$(eval $$(call lu-master-vars,$(1)))
 $$(eval $$(call lu-master-rules,$(1)))
endef
##########################################################

#$(warning $(call LU_RULES,example))
$(eval $(call lu-addtovar-global,MASTERS,\
	$$(shell grep -l '\\documentclass' *.tex 2>/dev/null | sed -e 's/\.tex$$$$//')))
ifneq ($(LU_REC_TARGET),)
_LU_DEF_MASTERS = $(LU_REC_MASTER)
_LU_DEF_FLAVORS = $(LU_REC_FLAVOR) $(FLAV_DEPFLAVOR_$(LU_REC_FLAVOR))
else
_LU_DEF_MASTERS = $(call lu-getvalues-global,MASTERS)
_LU_DEF_FLAVORS = $(sort $(foreach master,$(_LU_DEF_MASTERS),\
	$(call lu-getvalues-master,FLAVORS,$(master))))
endif

$(foreach flav, $(_LU_DEF_FLAVORS), $(eval $(call lu-define-flavor,$(flav))))
$(foreach master, $(_LU_DEF_MASTERS), $(eval $(call lu-master-vars,$(master))))
$(foreach flav, $(_LU_FLAVORS_DEFINED), $(eval $(call lu-flavor-rules,$(flav))))
$(foreach master, $(_LU_DEF_MASTERS), $(eval $(call lu-master-rules,$(master))))

##################################################################""
# Gestion des subfigs

%.subfig.mk: %.subfig %.fig
	$(COMMON_PREFIX)$(call lu-call-prog,GENSUBFIG) \
		-p '$$(COMMON_PREFIX)$(call lu-call-prog,FIGDEPTH) < $$< > $$@' \
		-s $*.subfig $*.fig < $^ > $@

%.subfig.mk: %.subfig %.svg
	$(COMMON_PREFIX)$(call lu-call-prog,GENSUBSVG) \
		-p '$$(COMMON_PREFIX)$(call lu-call-prog,SVGDEPTH) < $$< > $$@' \
		-s $*.subfig $*.svg < $^ > $@

clean::
	$(call lu-clean,$(FIGS2CREATE_LIST))
	$(call lu-clean,$(FIGS2CREATE_LIST:%.fig=%.pstex))
	$(call lu-clean,$(FIGS2CREATE_LIST:%.fig=%.pstex_t))
	$(call lu-clean,$(FIGS2CREATE_LIST:%.fig=%.$(_LU_PDFTEX_EXT)))
	$(call lu-clean,$(FIGS2CREATE_LIST:%.fig=%.pdftex_t))
	$(call lu-clean,$(FIGS2CREATE_LIST:%.svg=%.pstex))
	$(call lu-clean,$(FIGS2CREATE_LIST:%.svg=%.pstex_t))
	$(call lu-clean,$(FIGS2CREATE_LIST:%.svg=%.$(_LU_PDFTEX_EXT)))
	$(call lu-clean,$(FIGS2CREATE_LIST:%.svg=%.pdftex_t))

.PHONY: LU_FORCE clean distclean
LU_FORCE:
	@echo "Previous compilation failed. Rerun needed"

#$(warning $(MAKEFILE))

distclean:: clean

%.eps: %.fig
	$(COMMON_PREFIX)$(call lu-call-prog,FIG2DEV) -L eps $< $@

%.pdf: %.fig
	$(COMMON_PREFIX)$(call lu-call-prog,FIG2DEV) -L pdf $< $@

%.pstex: %.fig
	$(COMMON_PREFIX)$(call lu-call-prog,FIG2DEV) -L pstex $< $@

%.pstex: %.svg
	$(COMMON_PREFIX)$(call lu-call-prog,SVG2DEV) -L pstex $< $@


.PRECIOUS: %.pstex
%.pstex_t: %.fig %.pstex
	$(COMMON_PREFIX)$(call lu-call-prog,FIG2DEV) -L pstex_t -p $*.pstex $< $@

%.pstex_t: %.svg %.pstex
	$(COMMON_PREFIX)$(call lu-call-prog,SVG2DEV) -L pstex_t -p $*.pstex $< $@


%.$(_LU_PDFTEX_EXT): %.fig
	$(COMMON_PREFIX)$(call lu-call-prog,FIG2DEV) -L pdftex $< $@

%.$(_LU_PDFTEX_EXT): %.svg
	$(COMMON_PREFIX)$(call lu-call-prog,SVG2DEV) -L pdftex $< $@

.PRECIOUS: %.$(_LU_PDFTEX_EXT)
%.pdftex_t: %.fig %.$(_LU_PDFTEX_EXT)
	$(COMMON_PREFIX)$(call lu-call-prog,FIG2DEV) -L pdftex_t -p $*.$(_LU_PDFTEX_EXT) $< $@

%.pdftex_t: %.svg %.$(_LU_PDFTEX_EXT)
	$(COMMON_PREFIX)$(call lu-call-prog,SVG2DEV) -L pdftex_t -p $*.$(_LU_PDFTEX_EXT) $< $@

%.pdf: %.eps
	$(COMMON_PREFIX)$(call lu-call-prog,EPSTOPDF) --filter < $< > $@

#########################################################################
# Les flavors
LU_REC_LEVEL ?= 1
ifneq ($(LU_REC_TARGET),)
export LU_REC_FLAVOR
export LU_REC_MASTER
export LU_REC_TARGET
export LU_REC_LEVEL
LU_REC_LOGFILE=$(LU_REC_MASTER).log
LU_REC_GENFILE=$(LU_REC_MASTER)$(call lu-getvalue-flavor,EXT,$(LU_REC_FLAVOR))

lu-rebuild-head=$(info *** Checking rebuild with rule '$(subst LU_rebuild_,,$@)')
lu-rebuild-needed=echo $(1) >> "$(LU_REC_GENFILE)_NEED_REBUILD" ;

.PHONY: $(addprefix LU_rebuild_,latex texdepends bibtex)
LU_rebuild_latex:
	$(call lu-rebuild-head)
	$(COMMON_HIDE)if grep -sq 'Rerun to get'\
		"$(LU_REC_LOGFILE)" ; then \
		$(call lu-rebuild-needed\
		,"$@: new run needed (LaTeX message 'Rerun to get...')") \
	fi

LU_rebuild_texdepends:
	$(call lu-rebuild-head)
	$(COMMON_HIDE)if grep -sq '^Package texdepends Warning: .* Check dependencies again.$$'\
		"$(LU_REC_LOGFILE)" ; then \
		$(call lu-rebuild-needed,"$@: new depends required") \
	fi

LU_rebuild_bibtopic:
	$(call lu-rebuild-head)
	$(COMMON_HIDE)sed -e '/^Package bibtopic Warning: Please (re)run BibTeX on the file(s):$$/,/^(bibtopic) *and after that rerun LaTeX./{s/^(bibtopic) *\([^ ]*\)$$/\1/p};d' \
				"$(LU_REC_LOGFILE)" | while read file ; do \
		touch $$file.aux ; \
		$(call lu-rebuild-needed,"bibtopic: $$file.bbl outdated") \
	done

LU_rebuild_bibtopic_undefined_references:
	$(call lu-rebuild-head)
	$(COMMON_HIDE)if grep -sq 'There were undefined references'\
		"$(MASTER_$(LU_REC_MASTER)).log" ; then \
		$(call lu-rebuild-needed,"$@: new run needed") \
	fi

.PHONY: LU_WATCH_FILES_SAVE LU_WATCH_FILES_RESTORE
LU_WATCH_FILES_SAVE:
	$(COMMON_HIDE)$(foreach file, $(sort \
		$(call lu-getvalues,WATCHFILES,$(LU_REC_MASTER),$(LU_REC_FLAVOR))), \
	    $(call lu-save-file,$(file),$(file).orig);)

LU_WATCH_FILES_RESTORE:
	$(COMMON_HIDE)$(foreach file, $(sort \
		$(call lu-getvalues,WATCHFILES,$(LU_REC_MASTER),$(LU_REC_FLAVOR))), \
	    $(call lu-cmprestaure-file,"$(file)","$(file).orig",\
		echo "New $(file) file" >> $(LU_REC_GENFILE)_NEED_REBUILD;\
		);)

endif

%.bbl: %.aux
	$(COMMON_PREFIX)$(call lu-call-prog,BIBTEX) $*

_LaTeX_Make_GROUPS=texmfscripts tex
_LaTeX_Make_texmfscripts = LaTeX.mk figdepth.py gensubfig.py svg2dev.py svgdepth.py latexfilter.py
_LaTeX_Make_texmfscripts_DIR = scripts/latex-make
_LaTeX_Make_tex = figlatex.sty pdfswitch.sty texdepends.sty texgraphicx.sty
_LaTeX_Make_tex_DIR = tex/latex/latex-make

.PHONY: LaTeX-Make-local-install LaTeX-Make-local-uninstall

LaTeX-Make-local-uninstall::
	$(if $(TEXMF_INSTALL_ROOT_DIR),,\
	$(error TEXMF_INSTALL_ROOT_DIR must be set when calling LaTeX-Make-local-uninstall))
	$(foreach g,$(_LaTeX_Make_GROUPS),\
		$(foreach f,$(_LaTeX_Make_$(g)), \
			$(LU_RM) $(TEXMF_INSTALL_ROOT_DIR)/$(_LaTeX_Make_$(g)_DIR)/$f && \
		) (rmdir $(TEXMF_INSTALL_ROOT_DIR)/$(_LaTeX_Make_$(g)_DIR) || true) && \
	) $(LU_RM) LaTeX.mk

LU_INSTALL_PKSEWHICH?=env -u TEXMFHOME kpsewhich
LaTeX-Make-local-install::
	$(if $(TEXMF_INSTALL_ROOT_DIR),,\
	$(error TEXMF_INSTALL_ROOT_DIR must be set when calling LaTeX-Make-local-install))
	$(if $(filter texmf,$(notdir $(TEXMF_INSTALL_ROOT_DIR))),,\
	$(if $(FORCE),,\
	$(warning TEXMF_INSTALL_ROOT_DIR does not end with 'texmf')\
	$(error Use FORCE=1 if you really want to use this value of TEXMF_INSTALL_ROOT_DIR)))
	$(foreach g,$(_LaTeX_Make_GROUPS),\
		mkdir -p $(TEXMF_INSTALL_ROOT_DIR)/$(_LaTeX_Make_$(g)_DIR) && \
		$(foreach f,$(_LaTeX_Make_$(g)), \
			$(LU_CP) -v $$($(LU_INSTALL_PKSEWHICH) -format $g $f)  $(TEXMF_INSTALL_ROOT_DIR)/$(_LaTeX_Make_$(g)_DIR) && \
	)) echo "Installation into $(TEXMF_INSTALL_ROOT_DIR) done."
	@echo "==> You must ensure your TEXMFHOME contains this path <=="

