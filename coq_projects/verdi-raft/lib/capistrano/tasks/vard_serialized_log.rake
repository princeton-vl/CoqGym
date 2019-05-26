namespace :vard_serialized_log do

  def vard_serialized_log_cluster
    cluster = roles(:node).collect do |node|
      "-node #{node.properties.name},#{node.hostname}:#{fetch(:vard_serialized_log_node_port)}"
    end
    cluster.join(' ')
  end

  def vardctl_serialized_log_cluster
    cluster = roles(:node).collect do |node|
      "#{node.hostname}:#{fetch(:vard_serialized_log_client_port)}"
    end
    cluster.join(',')
  end

  def vard_serialized_log_snapshot_path
    "#{shared_path}/extraction/vard-serialized-log/tmp/snapshot"
  end

  def vard_serialized_log_clog_path
    "#{shared_path}/extraction/vard-serialized-log/tmp/log"
  end

  def vard_serialized_log_count_path
    "#{shared_path}/extraction/vard-serialized-log/tmp/count"
  end

  def vard_serialized_log_log_path
    "#{shared_path}/extraction/vard-serialized-log/log/vard-serialized-log.log"
  end

  def vard_serialized_log_pidfile_path
    "#{current_path}/extraction/vard-serialized-log/tmp/vard-serialized-log.pid"
  end
  
  desc 'start vard-serialized-log'
  task :start do
    on roles(:node) do |node|
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{vard_serialized_log_pidfile_path}",
        '--background',
        "--chdir #{current_path}/extraction/vard-serialized-log",

        '--startas /bin/bash',
        "-- -c 'exec ./vardserlog.native -me #{node.properties.name} -port #{fetch(:vard_serialized_log_client_port)} -dbpath #{current_path}/extraction/vard-serialized-log/tmp #{vard_serialized_log_cluster} > log/vard-serialized-log.log 2>&1'"
    end
  end

  desc 'stop vard-serialized-log'
  task :stop do
    on roles(:node) do
      execute '/sbin/start-stop-daemon',
        '--stop',
        '--oknodo',
        "--pidfile #{vard_serialized_log_pidfile_path}"
    end
  end

  desc 'tail vard-serialized-log log'
  task :tail_log do
    on roles(:node) do
      execute 'tail', '-n 20', vard_serialized_log_log_path
    end
  end

  desc 'truncate vard log'
  task :truncate_log do
    on roles(:node) do
      execute 'truncate', '-s 0', vard_serialized_log_log_path
    end
  end

  desc 'remove command log'
  task :remove_clog do
    on roles(:node) do
      execute 'rm', '-f', vard_serialized_log_clog_path
    end
  end

  desc 'remove snapshot'
  task :remove_snapshot do
    on roles(:node) do
      execute 'rm', '-f', vard_serialized_log_snapshot_path
    end
  end

  desc 'remove count'
  task :remove_count do
    on roles(:node) do
      execute 'rm', '-f', vard_serialized_log_count_path
    end
  end

  desc 'clean out volatile files'
  task :clean do
    on roles(:node) do
      execute 'rm', '-f', vard_serialized_log_clog_path
      execute 'rm', '-f', vard_serialized_log_snapshot_path
      execute 'rm', '-f', vard_serialized_log_count_path
      execute 'truncate', '-s 0', vard_serialized_log_log_path
    end
  end

  desc 'get status'
  task :status do
    run_locally do
      info %x(python2.7 extraction/vard-serialized-log/bench/vardctl.py --cluster #{vardctl_serialized_log_cluster} status)
    end
  end

  desc 'get status remote'
  task :status_remote do
    on roles(:client) do
      execute 'python2.7',
        "#{current_path}/extraction/vard-serialized-log/bench/vardctl.py",
        "--cluster #{vardctl_serialized_log_cluster}",
        'status'
    end
  end

  desc 'put key-value pair'
  task :put do
    run_locally do
      info %x(python2.7 extraction/vard-serialized-log/bench/vardctl.py --cluster #{vardctl_serialized_log_cluster} put #{ENV['KEY']} #{ENV['VALUE']})
    end
  end

  desc 'put key-value pair remote'
  task :put_remote do
    on roles(:client) do
      execute 'python2.7',
        "#{current_path}/extraction/vard-serialized-log/bench/vardctl.py",
        "--cluster #{vardctl_serialized_log_cluster}",
        'put',
        ENV['KEY'],
        ENV['VALUE']
    end
  end

  desc 'get value for key'
  task :get do
    run_locally do
      info %x(python2.7 extraction/vard-serialized-log/bench/vardctl.py --cluster #{vardctl_serialized_log_cluster} get #{ENV['KEY']})
    end
  end

  desc 'get value for key remote'
  task :get_remote do
    on roles(:client) do
      execute 'python2.7',
        "#{current_path}/extraction/vard-serialized-log/bench/vardctl.py",
        "--cluster #{vardctl_serialized_log_cluster}",
        'get',
        ENV['KEY']
    end
  end

  desc 'experiment 1'
  task :experiment_1 do
    names = roles(:node).collect { |node| node.properties.name }

    # 0. truncate logs
    Rake::Task['vard_serialized_log:truncate_log'].execute

    # 1. start up whole ring
    Rake::Task['vard_serialized_log:start'].execute

    # 2. pause 20 seconds
    sleep(5)

    # 3. send queries
    f = File.open('words50.txt')
    words = f.readlines
    for i in (1..50)
      ENV['KEY'] = words.sample.strip
      ENV['VALUE'] = words.sample.strip
      Rake::Task['vard_serialized_log:put_remote'].execute
    end
    
    # 4. stop ring
    Rake::Task['vard_serialized_log:stop'].execute
  end
end

