APA_VERSION=0.47.0
APA_RELEASE_URL=https://github.com/apalache-mc/apalache/releases/download/v${APA_VERSION}/apalache-${APA_VERSION}.tgz
APA=apalache-${APA_VERSION}
APA_ARCHIVE=$(APA).tgz
TLA_TOOLS_JAR=tla2tools.jar
TLA_TOOLS_JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
TLC_WORKERS=20
TLC_OFFHEAP_MEMORY=35G
TLC_HEAP=13G
STANDARD_MODULES=tla2sany/StandardModules/

all:

$(APA):
	wget --no-check-certificate --content-disposition $(APA_RELEASE_URL)
	tar -xzf $(APA_ARCHIVE)

$(TLA_TOOLS_JAR):
	wget --no-check-certificate --content-disposition -O $@ $(TLA_TOOLS_JAR_URL)

# Don't redownload stuff every time
.PRECIOUS: $(APA) $(TLA_TOOLS_JAR)

$(STANDARD_MODULES)/Variants.tla:
	jar -xf $(APA)/lib/apalache.jar tla2sany/StandardModules/

test: $(APA)
	$(APA)/bin/apalache-mc typecheck ApaBalloting.tla

abstractballoting-safety: $(APA)
	APA=$(APA) ./check.sh -inductive Invariant AbstractBalloting

balloting-refinement: $(TLA_TOOLS_JAR) $(STANDARD_MODULES)/Variants.tla
	java -Xmx${TLC_HEAP} -XX:+UseParallelGC -XX:MaxDirectMemorySize=${TLC_OFFHEAP_MEMORY} -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -Dtlc2.tool.ModelChecker.BAQueue=true -cp tla2tools.jar:${STANDARD_MODULES} tlc2.TLC -workers ${TLC_WORKERS} -checkpoint 30 -generateSpecTE TLCBalloting.tla

%.pdf: %.tla
	java -cp tla2tools.jar tla2tex.TLA -shade -ps -latexCommand pdflatex $<

PDF_FILES := Balloting.pdf AbstractBalloting.pdf Nomination.pdf NominationPlusCal.pdf
typeset: $(PDF_FILES)

.PHONY: abstract-scp-safety balloting-refinement typeset all
