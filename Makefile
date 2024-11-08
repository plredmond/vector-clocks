TLA_TOOLS_JAR=tla2tools.jar
TLA_TOOLS_JAR_URL=https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
TLC_WORKERS=4
TLC_OFFHEAP_MEMORY=10G
TLC_HEAP=5G

all:

tlc: $(TLA_TOOLS_JAR)
	java -Xmx${TLC_HEAP} -XX:+UseParallelGC -XX:MaxDirectMemorySize=${TLC_OFFHEAP_MEMORY} -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -Dtlc2.tool.ModelChecker.BAQueue=true -jar tla2tools.jar -workers ${TLC_WORKERS} VectorClocks.tla

$(TLA_TOOLS_JAR):
	wget --no-check-certificate --content-disposition -O $@ $(TLA_TOOLS_JAR_URL)

# Don't redownload stuff every time
.PRECIOUS: $(TLA_TOOLS_JAR)

%.pdf: %.tla
	java -cp tla2tools.jar tla2tex.TLA -shade -ps -latexCommand pdflatex $<

PDF_FILES := VectorClocks.pdf Utils.pdf

typeset: $(PDF_FILES)

.PHONY: typeset all
