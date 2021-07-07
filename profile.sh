touch ./callgrind.out. && \

rm ./callgrind.out.* && \

./compile.sh && \

valgrind --tool=callgrind --read-inline-info=yes \
    --dump-instr=yes --collect-jumps=yes -v \
    --num-callers=500 ./mreg && \

kcachegrind ./callgrind.out.*