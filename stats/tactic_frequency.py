import json


with open('./tactic_space.json', 'r') as f: tactic_space = json.load(f)["full"]

total_count = {}
frequencies = {}
total = 0

for tactic in tactic_space:
    total_count[tactic] = 0
    frequencies[tactic] = 0

with open("all_tactics.txt") as f:
    for proof_script in f:
        proof_commands = proof_script.split(" ")
        for command in proof_commands:
            if command in total_count:
                total += 1
                total_count[command] += 1

print(total_count)
print(total)

for k, v in total_count.items():
    frequencies[k] = v/total

print(frequencies)