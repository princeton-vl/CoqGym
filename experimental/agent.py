import torch, os
from utils import log
from progressbar import ProgressBar
import json
import gc


class Agent:

    def __init__(self, model, optimizer, dataloader, opts):
        self.model = model
        self.optimizer = optimizer
        self.dataloader = dataloader
        self.opts = opts
        self.projs_split = json.load(open(opts.projs_split))


    def train(self, n_epoch):
        self.model.train()

        bar = ProgressBar(max_value=len(self.dataloader["train"]))
        
        for i, data_batch in enumerate(self.dataloader["train"]):

            loss = self.model(data_batch)

            self.optimizer.zero_grad()
            loss.backward()
            self.optimizer.step()
            gc.collect()
            bar.update(i)
        
        log("\ntraining losses: %f" % loss)


    def save(self, n_epoch, dirname):
        torch.save(
            {
                "state_dict": self.model.state_dict(),
                "n_epoch": n_epoch,
                "optimizer": self.optimizer.state_dict(),
            },
            os.path.join(dirname, "model_%03d.pth" % n_epoch),
        )
