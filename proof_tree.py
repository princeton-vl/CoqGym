import pdb


class ProofNode:

    def __init__(self, parent, goal_id):
        'A ProofNode is an intermediate goal during proofs'
        self.parent = parent
        self.goal_id = goal_id
        self.children = []


    def to_dict(self):
        return {'goal_id': self.goal_id, 'children': [c.to_dict() for c in self.children]}


class ProofTree:

    def __init__(self, steps, goals):
        self.root = ProofNode(None, steps[0]['goal_ids']['fg'][0])
        frontier = {self.root.goal_id: self.root}
        for i, step in enumerate(steps[:-1]):
            next_step = steps[i + 1]
            goals_pre = set(step['goal_ids']['fg'] + step['goal_ids']['bg'])
            goals_post = set(next_step['goal_ids']['fg'] + next_step['goal_ids']['bg'])
            if goals_pre == goals_post:
                continue
            decomposed_goals = list(goals_pre - goals_post)
            new_goals = list(goals_post - goals_pre)
            assert len(decomposed_goals) == 1
            node = frontier.pop(decomposed_goals[0])
            frontier.update({child.goal_id: child for child in self.expand(node, new_goals)})


    def expand(self, node, new_goals):
        assert node.children == []
        for g in new_goals:
            node.children.append(ProofNode(node, g))
        return node.children


    def to_dict(self):
        return self.root.to_dict()
            
