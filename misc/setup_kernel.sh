# fix frequency
cpupower frequency-set -g performance

# disable THP
echo never | tee /sys/kernel/mm/transparent_hugepage/enabled

# disable alsr
echo 0 | sudo tee /proc/sys/kernel/randomize_va_space


echo 1 > /proc/sys/kernel/perf_event_paranoid
