date
#!/bin/bash
maude <<EOF
load maude-npa.maude
load signed_dh.maude
red genGrammars .
red run(0) .
red summary(1) .
red summary(2) .
red summary(3) .
red summary(4) .
red summary(5) .
red summary(6) .
red summary(7) .
red summary(8) .
red summary(9) .
red summary(10) .
red summary(11) .
red summary(12) .
red run(1) .
red run(2) .
red run(3) .
red run(4) .
red run(5) .
red run(6) .
red run(7) .
red run(8) .
red run(9) .
red run(10) .
red run(11) .
red run(12) .
EOF
date
