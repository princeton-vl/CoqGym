namespace :vard_serialized do

  def vard_serialized_cluster
    cluster = roles(:node).collect do |node|
      "-node #{node.properties.name},#{node.hostname}:#{fetch(:vard_serialized_node_port)}"
    end
    cluster.join(' ')
  end

  def vardctl_serialized_cluster
    cluster = roles(:node).collect do |node|
      "#{node.hostname}:#{fetch(:vard_serialized_client_port)}"
    end
    cluster.join(',')
  end

  def vard_serialized_snapshot_path
    "#{shared_path}/extraction/vard-serialized/tmp/snapshot.bin"
  end

  def vard_serialized_clog_path
    "#{shared_path}/extraction/vard-serialized/tmp/clog.bin"
  end

  def vard_serialized_log_path
    "#{shared_path}/extraction/vard-serialized/log/vard-serialized.log"
  end

  def vard_serialized_pidfile_path
    "#{current_path}/extraction/vard-serialized/tmp/vard-serialized.pid"
  end
  
  desc 'start vard-serialized'
  task :start do
    on roles(:node) do |node|
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{vard_serialized_pidfile_path}",
        '--background',
        "--chdir #{current_path}/extraction/vard-serialized",
        '--startas /bin/bash',
        "-- -c 'exec ./vardserialized.native -me #{node.properties.name} -port #{fetch(:vard_serialized_client_port)} -dbpath #{current_path}/extraction/vard-serialized/tmp #{vard_serialized_cluster} > log/vard-serialized.log 2>&1'"
    end
  end

  desc 'stop vard-serialized'
  task :stop do
    on roles(:node) do
      execute '/sbin/start-stop-daemon', 
        '--stop',
        '--oknodo',
        "--pidfile #{vard_serialized_pidfile_path}"
    end
  end

  desc 'tail vard-serialized log'
  task :tail_log do
    on roles(:node) do
      execute 'tail', '-n 20', vard_serialized_log_path
    end
  end

  desc 'truncate vard log'
  task :truncate_log do
    on roles(:node) do
      execute 'truncate', '-s 0', vard_serialized_log_path
    end
  end

  desc 'remove command log'
  task :remove_clog do
    on roles(:node) do
      execute 'rm', '-f', vard_serialized_clog_path
    end
  end

  desc 'remove snapshot'
  task :remove_snapshot do
    on roles(:node) do
      execute 'rm', '-f', vard_serialized_snapshot_path
    end
  end

  desc 'clean out volatile files'
  task :clean do
    on roles(:node) do
      execute 'rm', '-f', vard_serialized_clog_path
      execute 'rm', '-f', vard_serialized_snapshot_path
      execute 'truncate', '-s 0', vard_serialized_log_path
    end
  end

  desc 'get status'
  task :status do
    run_locally do
      info %x(python2.7 extraction/vard-serialized/bench/vardctl.py --cluster #{vardctl_serialized_cluster} status)
    end
  end

  desc 'get status remote'
  task :status_remote do
    on roles(:client) do
      execute 'python2.7',
        "#{current_path}/extraction/vard-serialized/bench/vardctl.py",
        "--cluster #{vardctl_serialized_cluster}",
        'status'
    end
  end

  desc 'put key-value pair'
  task :put do
    run_locally do
      info %x(python2.7 extraction/vard-serialized/bench/vardctl.py --cluster #{vardctl_serialized_cluster} put #{ENV['KEY']} #{ENV['VALUE']})
    end
  end

  desc 'put key-value pair remote'
  task :put_remote do
    on roles(:client) do
      execute 'python2.7',
        "#{current_path}/extraction/vard-serialized/bench/vardctl.py",
        "--cluster #{vardctl_serialized_cluster}",
        'put',
        ENV['KEY'],
        ENV['VALUE']
    end
  end

  desc 'get value for key'
  task :get do
    run_locally do
      info %x(python2.7 extraction/vard-serialized/bench/vardctl.py --cluster #{vardctl_serialized_cluster} get #{ENV['KEY']})
    end
  end

  desc 'get value for key remote'
  task :get_remote do
    on roles(:client) do
      execute 'python2.7',
        "#{current_path}/extraction/vard-serialized/bench/vardctl.py",
        "--cluster #{vardctl_serialized_cluster}",
        'get',
        ENV['KEY']
    end
  end

end
