namespace :compilation do

  desc 'configure and compile'
  task :build do
    on roles(:node) do
      within release_path do
        execute './configure'
        execute :make,
          "-j #{fetch(:make_jobs)}",
          'vard',
          'vard-serialized',
          'vard-log',
          'vard-serialized-log'
      end
    end
  end
  
  desc 'compile'
  task :compile do
    on roles(:node) do
      within release_path do
        execute :make,
          "-j #{fetch(:make_jobs)}",
          'vard',
          'vard-serialized',
          'vard-log',
          'vard-serialized-log'
      end
    end
  end

end

after 'deploy:updated', 'compilation:build'
