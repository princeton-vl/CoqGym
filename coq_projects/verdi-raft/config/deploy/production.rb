# server-based syntax
# ======================
# Defines a single server with a list of roles and multiple properties.
# You can define all roles on a single server, or split them:

# server "example.com", user: "deploy", roles: %w{app db web}, my_property: :my_value
# server "example.com", user: "deploy", roles: %w{app web}, other_property: :other_value
# server "db.example.com", user: "deploy", roles: %w{db}

server 'discoberry01.cs.washington.edu', user: 'pi', name: '0', roles: %w{node client}
server 'discoberry02.cs.washington.edu', user: 'pi', name: '1', roles: %w{node}
server 'discoberry03.cs.washington.edu', user: 'pi', name: '2', roles: %w{node}
server 'discoberry04.cs.washington.edu', user: 'pi', name: '3', roles: %w{node}
server 'discoberry05.cs.washington.edu', user: 'pi', name: '4', roles: %w{node}
server 'discoberry06.cs.washington.edu', user: 'pi', name: '5', roles: %w{node}
server 'discoberry07.cs.washington.edu', user: 'pi', name: '6', roles: %w{node}
server 'discoberry08.cs.washington.edu', user: 'pi', name: '7', roles: %w{node}
server 'discoberry09.cs.washington.edu', user: 'pi', name: '8', roles: %w{node}
server 'discoberry10.cs.washington.edu', user: 'pi', name: '9', roles: %w{node}

# role-based syntax
# ==================

# Defines a role with one or multiple servers. The primary server in each
# group is considered to be the first unless any hosts have the primary
# property set. Specify the username and a domain or IP for the server.
# Don't use `:all`, it's a meta role.

# role :app, %w{deploy@example.com}, my_property: :my_value
# role :web, %w{user1@primary.com user2@additional.com}, other_property: :other_value
# role :db,  %w{deploy@example.com}

# Configuration
# =============
# You can set any configuration variable like in config/deploy.rb
# These variables are then only loaded and set in this stage.
# For available Capistrano configuration variables see the documentation page.
# http://capistranorb.com/documentation/getting-started/configuration/
# Feel free to add new variables to customise your setup.

set :vard_log_node_port, 9500
set :vard_log_client_port, 8500

set :vard_node_port, 9000
set :vard_client_port, 8000

set :vard_serialized_log_node_port, 7500
set :vard_serialized_log_client_port, 6500

set :vard_serialized_node_port, 7000
set :vard_serialized_client_port, 6000

set :make_jobs, 2

# Custom SSH Options
# ==================
# You may pass any option but keep in mind that net/ssh understands a
# limited set of options, consult the Net::SSH documentation.
# http://net-ssh.github.io/net-ssh/classes/Net/SSH.html#method-c-start
#
# Global options
# --------------
#  set :ssh_options, {
#    keys: %w(/home/rlisowski/.ssh/id_rsa),
#    forward_agent: false,
#    auth_methods: %w(password)
#  }
#
# The server-based syntax can be used to override options:
# ------------------------------------
# server "example.com",
#   user: "user_name",
#   roles: %w{web app},
#   ssh_options: {
#     user: "user_name", # overrides user setting above
#     keys: %w(/home/user_name/.ssh/id_rsa),
#     forward_agent: false,
#     auth_methods: %w(publickey password)
#     # password: "please use keys"
#   }
