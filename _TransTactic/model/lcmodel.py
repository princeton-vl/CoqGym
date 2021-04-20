import json, torch
import torch.nn as nn
from helpers import get_lc_targets, get_pred_lc
from transformers import BertConfig, BertForSequenceClassification
from transformers import BertTokenizer, BasicTokenizer, PreTrainedTokenizer

class TransLCModel(nn.Module):
    def __init__(self, opts):
        super(TransLCModel, self).__init__()
        self.opts = opts
        with open(self.opts.tactics) as f:
            self.tactics = json.load(f)

        self.tokenizer = BertTokenizer.from_pretrained("bert-base-cased")
        self.config = BertConfig(hidden_dropout_prob=self.opts.dropout, 
                                 attention_probs_dropout_prob=self.opts.dropout,
                                 num_labels = 10,
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

        lc_texts = [[c["text"] for c in lc] for lc in batch["local_context"]]
        lc_ids = [[c["ident"] for c in lc] for lc in batch["local_context"]]
        lc_texts = lc_texts[0]
        lc_ids = lc_ids[0]
        
        for i, txt in enumerate(lc_texts):
            if txt == None:
                lc_texts[i] = "None"
        
        texts = goal_texts + lc_texts
        bert_input = texts[0]
        for text in texts[1:]:
            bert_input = f"{bert_input}. AND. {text}"

        targets, trues = get_lc_targets(self.opts, batch)
        logits, loss = self.go_bert([bert_input], targets)
        
        probs = self.softmax(logits)
        preds = get_pred_lc(self.tactics,  batch, probs)
        print(probs)
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

        lc_texts = [c["text"] for c in lc]
        for i, txt in enumerate(lc_texts):
            if txt == None:
                lc_texts[i] = "None"

        texts = goal_text + lc_texts
        bert_input = texts[0]
        for text in texts[1:]:
            bert_input = f"{bert_input}. AND. {text}"

        logits, _ = self.go_bert([bert_input], None)

        probs = self.softmax(logits)

        return probs