# -----------------------------------------------------------------------------
#
# (c) 2009 The University of Glasgow
#
# This file is part of the GHC build system.
#
# To understand how the build system works and how to modify it, see
#      http://hackage.haskell.org/trac/ghc/wiki/Building/Architecture
#      http://hackage.haskell.org/trac/ghc/wiki/Building/Modifying
#
# -----------------------------------------------------------------------------


libffi_STAMP_CONFIGURE = libffi/stamp.ffi.configure
libffi_STAMP_BUILD     = libffi/stamp.ffi.build
libffi_STAMP_INSTALL   = libffi/stamp.ffi.install

libffi_STATIC_LIB  = libffi/build/inst/lib/libffi.a
ffi_HEADER         = rts/dist/build/ffi.h

ifneq "$(BINDIST)" "YES"
$(libffi_STAMP_CONFIGURE):
	"$(RM)" $(RM_OPTS_REC) $(LIBFFI_DIR) libffi/build
	cat ghc-tarballs/libffi/libffi*.tar.gz | $(GZIP_CMD) -d | { cd libffi && $(TAR_CMD) -xf - ; }
	mv libffi/libffi-* libffi/build

# We have to fake a non-working ln for configure, so that the fallback
# option (cp -p) gets used instead.  Otherwise the libffi build system
# will use cygwin symbolic links which cannot be read by mingw gcc.
	chmod +x libffi/ln

# Because -Werror may be in SRC_CC_OPTS/SRC_LD_OPTS, we need to turn
# warnings off or the compilation of libffi might fail due to warnings
	cd libffi && \
	    PATH=$(TOP)/libffi:$$PATH; \
	    export PATH; \
	    cd build && \
	    CC=$(CC_STAGE1) \
	    LD=$(LD) \
	    AR=$(AR_STAGE1) \
	    NM=$(NM) \
        CFLAGS="$(SRC_CC_OPTS) $(CONF_CC_OPTS_STAGE1) -w" \
        LDFLAGS="$(SRC_LD_OPTS) $(CONF_GCC_LINKER_OPTS_STAGE1) -w" \
        "$(SHELL)" configure \
	          --prefix=$(TOP)/libffi/build/inst \
	          --with-pic \
	          --enable-static=yes \
	          --enable-shared=no \
	          --host=$(HOSTPLATFORM) --build=$(BUILDPLATFORM)

	# wc on OS X has spaces in its output, which libffi's Makefile
	# doesn't expect, so we tweak it to sed them out
	mv libffi/build/Makefile libffi/build/Makefile.orig
	sed "s#wc -w#wc -w | sed 's/ //g'#" < libffi/build/Makefile.orig > libffi/build/Makefile

	touch $@

$(libffi_STAMP_BUILD): $(libffi_STAMP_CONFIGURE)
	$(MAKE) -C libffi/build MAKEFLAGS=
	touch $@

$(libffi_STAMP_INSTALL): $(libffi_STAMP_BUILD)
	$(MAKE) -C libffi/build MAKEFLAGS= install
	touch $@

$(libffi_STATIC_LIB): $(libffi_STAMP_INSTALL)
	@test -f $@ || { echo "$< exists, but $@ does not."; echo "Suggest removing $<."; exit 1; }

$(ffi_HEADER): $(libffi_STAMP_INSTALL) | $$(dir $$@)/.
	cp libffi/build/inst/lib/libffi-*/include/ffitarget.h $(dir $@)
	cp libffi/build/inst/lib/libffi-*/include/ffi.h $@

$(eval $(call clean-target,libffi,, \
    libffi/build libffi/stamp.ffi.* libffi/dist-install))

endif

