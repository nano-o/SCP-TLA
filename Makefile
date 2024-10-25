APA_VERSION=0.47.0
APA_RELEASE_URL=https://github.com/apalache-mc/apalache/releases/download/v${APA_VERSION}/apalache-${APA_VERSION}.tgz
APA=apalache-${APA_VERSION}
APA_ARCHIVE=$(APA).tgz
TLC_JAR=tla2tools.jar
TLC_JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
TLC_WORKERS=4
TLC_OFFHEAP_MEMORY=10G
TLC_HEAP=10G

$(APA):
	wget --no-check-certificate --content-disposition $(APA_RELEASE_URL)
	tar -xzf $(APA_ARCHIVE)

$(TLC_JAR):
	wget --no-check-certificate --content-disposition -O $@ $(TLC_JAR_URL)

# Don't redownload stuff every time
.PRECIOUS: $(APA) $(TLC_JAR)

abstractballoting-safety: $(APA)
	APA=$(APA) ./check.sh -inductive Invariant AbstractBalloting

balloting-refinement: $(TLC_JAR)
	java -Xmx${TLC_HEAP} -XX:+UseParallelGC -XX:MaxDirectMemorySize=${TLC_OFFHEAP_MEMORY} -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -Dtlc2.tool.ModelChecker.BAQueue=true -jar tla2tools.jar -workers ${TLC_WORKERS} -checkpoint 30 -tool TLCBalloting.tla


.PHONY: abstract-scp-safety
