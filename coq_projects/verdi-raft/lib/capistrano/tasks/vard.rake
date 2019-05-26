namespace :vard do

  def vard_cluster
    cluster = roles(:node).collect do |node|
      "-node #{node.properties.name},#{node.hostname}:#{fetch(:vard_node_port)}"
    end
    cluster.join(' ')
  end

  def vardctl_cluster
    cluster = roles(:node).collect do |node|
      "#{node.hostname}:#{fetch(:vard_client_port)}"
    end
    cluster.join(',')
  end

  def vard_snapshot_path
    "#{shared_path}/extraction/vard/tmp/snapshot.bin"
  end

  def vard_clog_path
    "#{shared_path}/extraction/vard/tmp/clog.bin"
  end

  def vard_log_path
    "#{shared_path}/extraction/vard/log/vard.log"
  end

  def vard_pidfile_path
    "#{shared_path}/extraction/vard/tmp/vard.pid"
  end

  desc 'start vard'
  task :start do
    on roles(:node) do |node|
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{vard_pidfile_path}",
        '--background',
        "--chdir #{current_path}/extraction/vard",
        '--startas /bin/bash',
        "-- -c 'exec ./vard.native -me #{node.properties.name} -port #{fetch(:vard_client_port)} -dbpath #{shared_path}/extraction/vard/tmp #{vard_cluster} > log/vard.log 2>&1'"
    end
  end

  desc 'stop vard'
  task :stop do
    on roles(:node) do
      execute '/sbin/start-stop-daemon', 
        '--stop',
        '--oknodo',
        "--pidfile #{vard_pidfile_path}"
    end
  end

  desc 'tail vard log'
  task :tail_log do
    on roles(:node) do
      execute 'tail', '-n 20', vard_log_path
    end
  end

  desc 'truncate vard log'
  task :truncate_log do
    on roles(:node) do
      execute 'truncate', '-s 0', vard_log_path
    end
  end

  desc 'remove command log'
  task :remove_clog do
    on roles(:node) do
      execute 'rm', '-f', vard_clog_path
    end
  end

  desc 'remove snapshot'
  task :remove_snapshot do
    on roles(:node) do
      execute 'rm', '-f', vard_snapshot_path
    end
  end

  desc 'clean out volatile files'
  task :clean do
    on roles(:node) do
      execute 'rm', '-f', vard_clog_path
      execute 'rm', '-f', vard_snapshot_path
      execute 'truncate', '-s 0', vard_log_path
    end
  end

  desc 'get status'
  task :status do
    run_locally do
      info %x(python2.7 extraction/vard/bench/vardctl.py --cluster #{vardctl_cluster} status)
    end
  end

  desc 'get status remote'
  task :status_remote do
    on roles(:client) do
      execute 'python2.7',
        "#{current_path}/extraction/vard/bench/vardctl.py",
        "--cluster #{vardctl_cluster}",
        'status'
    end
  end

  desc 'put key-value pair'
  task :put do
    run_locally do
      info %x(python2.7 extraction/vard/bench/vardctl.py --cluster #{vardctl_cluster} put #{ENV['KEY']} #{ENV['VALUE']})
    end
  end

  desc 'put key-value pair remote'
  task :put_remote do
    on roles(:client) do
      execute 'python2.7',
        "#{current_path}/extraction/vard/bench/vardctl.py",
        "--cluster #{vardctl_cluster}",
        'put',
        ENV['KEY'],
        ENV['VALUE']
    end
  end

  desc 'get value for key'
  task :get do
    run_locally do
      info %x(python2.7 extraction/vard/bench/vardctl.py --cluster #{vardctl_cluster} get #{ENV['KEY']})
    end
  end

  desc 'get value for key remote'
  task :get_remote do
    on roles(:client) do
      execute 'python2.7',
        "#{current_path}/extraction/vard/bench/vardctl.py",
        "--cluster #{vardctl_cluster}",
        'get',
        ENV['KEY']
    end
  end
  desc 'experiment 1'
  task :experiment_1 do
    names = roles(:node).collect { |node| node.properties.name }

    # 0. truncate logs
    Rake::Task['vard:truncate_log'].execute

    # 1. start up whole ring
    Rake::Task['vard:start'].execute

    # 2. pause 20 seconds
    sleep(5)

    # 3. send queries
    f = File.open('words50.txt')
    words = f.readlines
    for i in (1..50)
      ENV['KEY'] = words.sample.strip
      ENV['VALUE'] = words.sample.strip
      Rake::Task['vard:put'].execute
    end
    
    # 4. stop ring
    Rake::Task['vard:stop'].execute
  end
end
