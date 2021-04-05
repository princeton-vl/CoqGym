import json, torch
import torch.nn as nn
from transformers import BertConfig, BertForSequenceClassification
from transformers import BertTokenizer, BasicTokenizer, PreTrainedTokenizer

class BERTModel(nn.Module):
    def __init__(self, opts):
        super(BERTModel, self).__init__()
        self.opts = opts
        with open(f'{opts.jsonpath}/tactic_groups.json', 'r') as f:
            self.tactic_groups = json.load(f)
        with open(f'{opts.jsonpath}/tactic_groups_reverse.json', 'r') as f: 
            self.tactic_groups_reverse = json.load(f)
        
  
                                 
        self.tokenizer = BertTokenizer.from_pretrained("bert-base-cased")
        
        self.config = BertConfig(hidden_dropout_prob=self.opts.dropout, 
                                 attention_probs_dropout_prob=self.opts.dropout,
                                 num_labels = len(self.tactic_groups),
                                 num_hidden_layers=self.opts.num_hidden,
                                 num_attention_heads=self.opts.num_attention,
                                 vocab_size = len(self.tokenizer))
                                 
        self.bert = BertForSequenceClassification(config=self.config)
        
    def forward(self, texts, labels):
                        
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
