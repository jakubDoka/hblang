afl-fuzz -i /home/mlokis/personal/zig/hblang/.zig-cache/o/0e04107b2ba7ec222ca565c88459075b/fuzz-cases -o /home/mlokis/personal/zig/hblang/.zig-cache/o/a1c0c4a0024f9744bb088d2785d0c92d/findings -S worker1 -x /home/mlokis/personal/zig/hblang/.zig-cache/o/0e04107b2ba7ec222ca565c88459075b/hblang.dict -- /home/mlokis/personal/zig/hblang/.zig-cache/o/dc1b80ba16a50db4138d4ff92006b073/fuzz &
afl-fuzz -i /home/mlokis/personal/zig/hblang/.zig-cache/o/0e04107b2ba7ec222ca565c88459075b/fuzz-cases -o /home/mlokis/personal/zig/hblang/.zig-cache/o/a1c0c4a0024f9744bb088d2785d0c92d/findings -S worker2 -x /home/mlokis/personal/zig/hblang/.zig-cache/o/0e04107b2ba7ec222ca565c88459075b/hblang.dict -- /home/mlokis/personal/zig/hblang/.zig-cache/o/dc1b80ba16a50db4138d4ff92006b073/fuzz &
afl-fuzz -i /home/mlokis/personal/zig/hblang/.zig-cache/o/0e04107b2ba7ec222ca565c88459075b/fuzz-cases -o /home/mlokis/personal/zig/hblang/.zig-cache/o/a1c0c4a0024f9744bb088d2785d0c92d/findings -S worker3 -x /home/mlokis/personal/zig/hblang/.zig-cache/o/0e04107b2ba7ec222ca565c88459075b/hblang.dict -- /home/mlokis/personal/zig/hblang/.zig-cache/o/dc1b80ba16a50db4138d4ff92006b073/fuzz &
afl-fuzz -i /home/mlokis/personal/zig/hblang/.zig-cache/o/0e04107b2ba7ec222ca565c88459075b/fuzz-cases -o /home/mlokis/personal/zig/hblang/.zig-cache/o/a1c0c4a0024f9744bb088d2785d0c92d/findings -M worker0 -x /home/mlokis/personal/zig/hblang/.zig-cache/o/0e04107b2ba7ec222ca565c88459075b/hblang.dict -- /home/mlokis/personal/zig/hblang/.zig-cache/o/dc1b80ba16a50db4138d4ff92006b073/fuzz &

sleep 5

killall afl-fuzz
