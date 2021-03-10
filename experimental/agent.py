import torch, os
from utils import log
from progressbar import ProgressBar
import json
import gc
import pickle

class Agent:

    def __init__(self, model, optimizer, dataloader, opts):
        self.model = model
        self.optimizer = optimizer
        self.dataloader = dataloader
        self.opts = opts
        self.projs_split = json.load(open(opts.projs_split))

    def save(self, n_epoch, dirname):
        torch.save(
            {
                "state_dict": self.model.state_dict(),
                "n_epoch": n_epoch,
                "optimizer": self.optimizer.state_dict(),
            },
            os.path.join(dirname, "model_%03d.pth" % n_epoch),
        )

    def train(self, n_epoch):
        self.model.train()

        bar = ProgressBar(max_value=len(self.dataloader["train"]))
        
        for i, data_batch in enumerate(self.dataloader["train"]):

            preds, true, loss = self.model(data_batch)

            self.optimizer.zero_grad()
            loss.backward()
            self.optimizer.step()
            gc.collect()
            bar.update(i)
        
        log("\ntraining losses: %f" % loss)
    
    def valid(self, n_epoch):
        self.model.eval()
        log("validating..")
        loss_avg = 0
        predictions = []
        num_correct = 0
        bar = ProgressBar(max_value=len(self.dataloader["valid"]))

        for i, data_batch in enumerate(self.dataloader["valid"]):
            preds, true, loss = self.model(data_batch)
            loss_avg += loss.item()

            for n in range(len(preds)):
                if preds[n] == true[n]:
                    num_correct += 1
                predictions.append({
                    "file_name": data_batch["file"][n],
                    "proof_name": data_batch["proof_name"][n],
                    "n_step": data_batch["n_step"][n],
                    "true": true[i],
                    "pred": preds[i],
                })
            gc.collect()
            bar.update(i)

        pickle.dump(
            predictions,
            open(
                os.path.join(
                    self.opts.log_dir, "predictions/pred_%03d.pickle" % n_epoch
                ),
                "wb",
            ),
        )

        loss_avg /= len(self.dataloader["valid"])
        log("\nvalidation losses: %f" % loss_avg)
        acc = num_correct / len(predictions)
        log("validation accuracy: %f" % acc)
        return loss_avg

    def evaluate_proxy(self, file):
        self.model.eval()
        proof_step = pickle.load(open(file, 'rb'))

        proof_step_prepped = {}
        proof_step_prepped["goal_ast"] = [proof_step["goal"]["ast"]]
        proof_step_prepped["local_context"] = [proof_step["local_context"]]
        proof_step_prepped["env"] = [proof_step["env"]]
        proof_step_prepped["tactic_str"] = [proof_step["tactic"]["text"]]

        preds, true, loss = self.model(proof_step_prepped)
        return preds, true
