APA_VERSION=0.47.2
APA_RELEASE_URL=https://github.com/apalache-mc/apalache/releases/download/v${APA_VERSION}/apalache-${APA_VERSION}.tgz
APA=apalache-${APA_VERSION}
APA_ARCHIVE=$(APA).tgz
TLA_TOOLS_JAR=tla2tools.jar
TLA_TOOLS_JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
TLC_WORKERS=8
TLC_OFFHEAP_MEMORY=10G
TLC_HEAP=5G
TLA_SPEC?=
TLC_CMD = java -Xmx${TLC_HEAP} -XX:+UseParallelGC -XX:MaxDirectMemorySize=${TLC_OFFHEAP_MEMORY} -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -Dtlc2.tool.ModelChecker.BAQueue=true -jar tla2tools.jar -workers ${TLC_WORKERS} -checkpoint 30

all:

$(APA):
	wget --no-check-certificate --content-disposition $(APA_RELEASE_URL)
	tar -xzf $(APA_ARCHIVE)

$(TLA_TOOLS_JAR):
	wget --no-check-certificate --content-disposition -O $@ $(TLA_TOOLS_JAR_URL)

# Don't redownload stuff every time
.PRECIOUS: $(APA) $(TLA_TOOLS_JAR)

abstractballoting-safety: $(APA)
	APA=$(APA) ./check.sh -inductive InductiveInvariant AbstractBalloting

balloting-refinement: $(TLA_TOOLS_JAR) TLCBalloting.cfg TLCBalloting.tla Balloting.tla AbstractBalloting.tla
	java -Xmx${TLC_HEAP} -XX:+UseParallelGC -XX:MaxDirectMemorySize=${TLC_OFFHEAP_MEMORY} -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -Dtlc2.tool.ModelChecker.BAQueue=true -jar tla2tools.jar -workers ${TLC_WORKERS} -checkpoint 30 -generateSpecTE TLCBalloting.tla

%.pdf: %.tla
	java -cp tla2tools.jar tla2tex.TLA -shade -ps -latexCommand pdflatex $<

PDF_FILES := Balloting.pdf AbstractBalloting.pdf Nomination.pdf NominationPlusCal.pdf AbstractBallotingWithPrepare.pdf ChainConsensus.pdf
typeset: $(PDF_FILES)

abwp-tlc: $(TLA_TOOLS_JAR)
	java -Xmx${TLC_HEAP} -XX:+UseParallelGC -XX:MaxDirectMemorySize=${TLC_OFFHEAP_MEMORY} -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -Dtlc2.tool.ModelChecker.BAQueue=true -jar tla2tools.jar -workers ${TLC_WORKERS} -checkpoint 30 -generateSpecTE TLCAbstractBallotingWithPrepare.tla

run-tlc: $(TLA_TOOLS_JAR) $(TLA_SPEC)
	@if [ -z "$(TLA_SPEC)" ]; then \
	  echo "Error: TLA_SPEC is not set. Use make run-tlc TLA_SPEC=YourSpec.tla"; \
	  exit 1; \
	fi
	$(TLC_CMD) $(TLA_SPEC)

abwp-apa-liveness-invariant: $(APA)
	APA=$(APA) ./check.sh -inductive LivenessInductiveInvariant AbstractBallotingWithPrepare

abwp-apa-safety: $(APA)
	APA=$(APA) ./check.sh -inductive AgreementInductiveInvariant AbstractBallotingWithPrepare

trans: $(TLA_TOOLS_JAR) $(TLA_SPEC)
	@if [ -z "$(TLA_SPEC)" ]; then \
	  echo "Error: TLA_SPEC is not set. Use make run-tlc TLA_SPEC=YourSpec.tla"; \
	  exit 1; \
	fi
	java -cp $(TLA_TOOLS_JAR) pcal.trans -nocfg $(TLA_SPEC)


sany: $(TLA_TOOLS_JAR) $(TLA_SPEC)
	@if [ -z "$(TLA_SPEC)" ]; then \
	  echo "Error: TLA_SPEC is not set. Use make run-tlc TLA_SPEC=YourSpec.tla"; \
	  exit 1; \
	fi
	java -cp $(TLA_TOOLS_JAR) tla2sany.SANY $(TLA_SPEC)

.PHONY: abstract-scp-safety balloting-refinement typeset all sany run-tlc trans abwp-tlc abwp-apa-safety abwp-apa-liveness-invariant
