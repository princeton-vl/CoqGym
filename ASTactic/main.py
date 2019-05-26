import torch
import torch.nn as nn
from torch.optim.lr_scheduler import ReduceLROnPlateau, StepLR
from options import parse_args
from dataloader import create_dataloader
from utils import log
from agent import Agent
from models.prover import Prover
import sys
import pdb

def main():

    # parse the options
    opts = parse_args()

    # create the dataloaders
    dataloader = {'train': create_dataloader('train_valid' if opts.no_validation else 'train', opts),
                  'valid': create_dataloader('valid', opts)}
    
    # create the model 
    model = Prover(opts)
    model.to(opts.device)
  
    # crete the optimizer
    optimizer = torch.optim.RMSprop(model.parameters(), lr=opts.learning_rate,
                                    momentum=opts.momentum,
                                    weight_decay=opts.l2)
    if opts.no_validation:
        scheduler = StepLR(optimizer, step_size=opts.lr_reduce_steps, gamma=0.1) 
    else:
        scheduler = ReduceLROnPlateau(optimizer, patience=opts.lr_reduce_patience, verbose=True)

    # load the checkpoint
    start_epoch = 0
    if opts.resume != None:
        log('loading model checkpoint from %s..' % opts.resume)
        if opts.device.type == 'cpu':
            checkpoint = torch.load(opts.resume, map_location='cpu')
        else:
            checkpoint = torch.load(opts.resume)
        model.load_state_dict(checkpoint['state_dict'])
        optimizer.load_state_dict(checkpoint['optimizer'])
        start_epoch = checkpoint['n_epoch'] + 1
        model.to(opts.device)

    agent = Agent(model, optimizer, dataloader, opts)

    best_acc = -1.
    for n_epoch in range(start_epoch, start_epoch + opts.num_epochs):
        log('EPOCH #%d' % n_epoch)
   
        # training
        loss_train = agent.train(n_epoch)

        # save the model checkpoint
        if n_epoch % opts.save_model_epochs == 0:
            agent.save(n_epoch, opts.checkpoint_dir)

        # validation
        if not opts.no_validation:
            loss_valid = agent.valid(n_epoch)

        # reduce the learning rate
        if opts.no_validation:
            scheduler.step()
        else:
            scheduler.step(loss_valid)


if __name__ == '__main__':
    main()
