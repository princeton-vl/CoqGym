import json, torch
import torch.nn as nn
from _SL.helpers import get_gc_targets, get_gc_pred
from transformers import BertConfig, BertForSequenceClassification
from transformers import BertTokenizer, BasicTokenizer, PreTrainedTokenizer

class TransGC(nn.Module):
    def __init__(self, opts):
        super(TransGC, self).__init__()
        self.opts = opts
        with open(self.opts.tactics) as f:
            self.tactics = json.load(f)

        self.tokenizer = BertTokenizer.from_pretrained("bert-base-cased")
        self.config = BertConfig(hidden_dropout_prob=self.opts.dropout, 
                                 attention_probs_dropout_prob=self.opts.dropout,
                                 num_labels = 10,
                                 num_hidden_layers=self.opts.num_hidden,
                                 num_attention_heads=self.opts.num_attention,
                                 vocab_size = 28996) #30522

        self.bert= BertForSequenceClassification.from_pretrained('bert-base-uncased', config=self.config)
        #self.bert = BertForSequenceClassification(config=self.config)
        self.softmax = nn.Softmax(dim=1)
        
    def forward(self, batch): 
        goal_texts = [goal['text'] for goal in batch['goal']]
        
        for i, txt in enumerate(goal_texts):
            if txt == None:
                goal_texts[i] = "none"

        gc_texts_s = [[c["text"] for c in gc] for gc in batch["env"]]
        
        bert_inputs = []
        for i, gc_texts in enumerate(gc_texts_s):
            bert_input = goal_texts[i]
            count = 1
            for gc_text in gc_texts:
                if gc_text == None:
                    gc_text = "none"
                
                bert_input = f"{bert_input}. {gc_text}"
                count += 1
            while count < 11:
                bert_input = f"{bert_input}. none"
                count += 1
            
            bert_inputs.append(bert_input)

        targets, trues = get_gc_targets(self.opts, batch)

        logits, loss = self.go_bert(bert_inputs, targets)
        
        probs = self.softmax(logits)
        preds = get_gc_pred(self.tactics, batch, probs)
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
            goal_text = "None"

        gc_texts = [c["text"] for c in gc]
        for i, txt in enumerate(gc_texts):
            if txt == None:
                gc_texts[i] = "None"

        texts = [goal_text] + gc_texts
        bert_input = texts[0]
        for text in texts[1:]:
            bert_input = f"{bert_input}. {text}"

        count = 1
        for text in texts[1:]:
            count += 1
            bert_input = f"{bert_input}. {text}"

        while count < 11:
            bert_input = f"{bert_input}. none"
            count += 1

        logits, _ = self.go_bert([bert_input], None)

        probs = self.softmax(logits)

        return probs[0]
