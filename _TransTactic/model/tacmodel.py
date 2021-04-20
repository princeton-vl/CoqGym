import json, torch
import torch.nn as nn
from helpers import get_tactic_targets, get_true_tactics, get_true_args, get_pred_tactics, prep_asts
from transformers import BertConfig, BertForSequenceClassification
from transformers import BertTokenizer, BasicTokenizer, PreTrainedTokenizer

class TransTacModel(nn.Module):
    def __init__(self, opts):
        super(TransTacModel, self).__init__()
        self.opts = opts
        with open(self.opts.tactics) as f:
            self.tactics = json.load(f)

        self.tokenizer = BertTokenizer.from_pretrained("bert-base-cased")
        self.config = BertConfig(hidden_dropout_prob=self.opts.dropout, 
                                 attention_probs_dropout_prob=self.opts.dropout,
                                 num_labels = len(self.tactics),
                                 num_hidden_layers=self.opts.num_hidden,
                                 num_attention_heads=self.opts.num_attention,
                                 vocab_size = len(self.tokenizer))
        self.bert = BertForSequenceClassification(config=self.config)
        self.softmax = nn.Softmax(dim=1)
        
    def forward(self, batch): 
        goal_texts = [goal['text'] for goal in batch['goal']]
        
        for i, txt in enumerate(goal_texts):
            if txt == None:
                goal_texts[i] = "None"

        targets = get_tactic_targets(self.opts, self.tactics, batch)

        logits, loss = self.go_bert(goal_texts, targets)
        
        trues = get_true_tactics(batch)
        probs = self.softmax(logits)
        preds = get_pred_tactics(self.tactics, probs)
        return preds, trues, loss

    def go_bert(self, texts, labels):
        encodings = self.tokenizer.batch_encode_plus(texts,
                                                     add_special_tokens=True,
                                                     return_attention_mask=True,
                                                     padding='max_length',
                                                     return_tensors='pt',
                                                     truncation=True,
                                                     max_length=self.opts.tokenizer_length)
                                                     
        tokens = encodings["input_ids"].to(self.opts.device)
        attention_masks = encodings["attention_mask"].to(self.opts.device)
    
        input = {"input_ids": tokens, "attention_mask": attention_masks, "labels": labels}
    
        output = self.bert(**input, output_hidden_states=True, output_attentions=True)
        
        return output.logits, output.loss

    def prove(self, goal, lc, gc):
        goal_text = goal['text']
        if goal_text == None:
            goal_texts[i] = "None"

        logits, _ = self.go_bert([goal_text], None)

        probs = self.softmax(logits)

        return probs