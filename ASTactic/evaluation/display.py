import sys
import json
import os
from glob import glob
from collections import defaultdict
import csv
import pdb

TIME_LIMIT = 600

num_success = defaultdict(int)
num_fail = defaultdict(int)
avg_time = 0

for f in glob(os.path.join(sys.argv[1], '*.json')):
    results = json.load(open(f))['results']
    for r in results:
        proj = r['filename'].split(os.path.sep)[2]
        if r['success'] and r['time'] <= TIME_LIMIT:
            num_success[proj] += 1
            avg_time += r['time']
        else:
            num_fail[proj] += 1

total_success = 0
total_fail = 0
for proj in set(num_success.keys()).union(set(num_fail.keys())):
    print('%50s:\t%.04f\t%d/%d' % (proj, num_success[proj] / (num_success[proj] + num_fail[proj]), num_success[proj], num_fail[proj]))
    total_success += num_success[proj]
    total_fail += num_fail[proj]

print('\nIN TOTAL:\t%.04f\t%d/%d' % (total_success / (total_success + total_fail), total_success, total_fail))
print('avg_time', avg_time / total_success)
