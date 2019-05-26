# config valid only for current version of Capistrano
lock "3.10.2"

set :application, 'vard'
set :repo_url, 'git@github.com:uwplse/verdi-raft.git'

# Default branch is :master
# ask :branch, `git rev-parse --abbrev-ref HEAD`.chomp

# Default deploy_to directory is /var/www/my_app_name
set :deploy_to, '/home/pi/lib/verdi-raft'

# Default value for :format is :airbrussh.
# set :format, :airbrussh

# You can configure the Airbrussh format using :format_options.
# These are the defaults.
# set :format_options, command_output: true, log_file: "log/capistrano.log", color: :auto, truncate: :auto
set :format_options, command_output: true, log_file: "log/capistrano.log", color: :auto, truncate: false

# Default value for :pty is false
# set :pty, true

# Default value for :linked_files is []
# append :linked_files, "config/database.yml", "config/secrets.yml"

# Default value for linked_dirs is []
# append :linked_dirs, "log", "tmp/pids", "tmp/cache", "tmp/sockets", "public/system"
append :linked_dirs,
  'extraction/vard/tmp',
  'extraction/vard/log',
  'extraction/vard-serialized/tmp',
  'extraction/vard-serialized/log',
  'extraction/vard-log/tmp',
  'extraction/vard-log/log',
  'extraction/vard-serialized-log/tmp',
  'extraction/vard-serialized-log/log'

# Default value for default_env is {}
# set :default_env, { path: "/opt/ruby/bin:$PATH" }
set :default_env, {}

# Default value for keep_releases is 5
set :keep_releases, 3
