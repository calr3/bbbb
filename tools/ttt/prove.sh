#!/bin/bash
# Upper-bound pipeline for one TTT domain:  tools/ttt/prove.sh N M CHAMPION_VALUE
#   1. tree search at 10^5 steps, holdouts rerun at 10^7 (ttt.c), and again with a wider
#      translated-cycler window (ttt_big);
#   2. bouncer certificates (bouncer_ttt.py);
#   3. inductive certificates with discovered lemmas (auto.py), then with larger regions;
#   4. combine.py: how many holdouts are certified, and the largest finite last use among them.
# Results go to results/N_M/ (or to $OUT).
set -e
cd "$(dirname "$0")"
N=$1; M=$2; BOUND=$3
D=${OUT:-results/${N}_${M}}; mkdir -p $D
gcc -O2 -o ttt ttt.c
sed -e 's/#define W 256 /#define W 4096 /' -e 's/#define R 1024 /#define R 8192 /' ttt.c > /tmp/ttt_big.c
gcc -O2 -o ttt_big /tmp/ttt_big.c
./ttt $N $M 100000 - $D/h1.txt > $D/search1.txt
./ttt $N $M 10000000 @$D/h1.txt $D/h2.txt > $D/search2.txt
cat $D/search1.txt $D/search2.txt
python3 bouncer_ttt.py $D/h2.txt $D/bouncer1.txt
grep fail $D/bouncer1.txt | cut -d' ' -f1 > $D/f1.txt
./ttt_big $N $M 10000000 @$D/f1.txt $D/h3.txt > $D/search3.txt
cut -d' ' -f1 $D/h3.txt | sort > $D/h3s.txt
sort $D/f1.txt | comm -23 - $D/h3s.txt | awk '{print $1, "decided translated-cycler"}' > $D/decided3.txt
python3 bouncer_ttt.py $D/h3.txt $D/bouncer2.txt
grep fail $D/bouncer2.txt | cut -d' ' -f1 > $D/f2.txt
AUTO_BUDGET=16 python3 auto.py $D/f2.txt $D/auto1.txt
grep fail $D/auto1.txt | cut -d' ' -f1 > $D/f3.txt
AUTO_IB=9 AUTO_IA=5 AUTO_BUDGET=40 python3 auto.py $D/f3.txt $D/auto2.txt
python3 combine.py $D/h2.txt $D/bouncer1.txt $D/decided3.txt $D/bouncer2.txt $D/auto1.txt \
    $D/auto2.txt --bound $BOUND | tee $D/summary.txt
