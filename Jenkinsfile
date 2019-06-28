pipeline {
  agent {
    dockerfile {
      additionalBuildArgs ''' \
        --build-arg UID=$(id -u) \
        --build-arg GID=$(id -g) \
      '''
    }
  }
  options {
    ansiColor('xterm')
  }
  stages{
    stage("Init title") {
      when { changeRequest() }
      steps {
        script {
          currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}"
        }
      }
    }
    stage('Build') {
      steps {
        sh '''
          . scripts/setenv
          export KOMPILE_FLAGS=-O2
          make -j4 profile-rule-parsing --output-sync=line
        '''
      }
      post { success {
        archiveArtifacts 'dist/timelogs.d/timelogs.csv'
      } }
    }
    stage('Re-Build with timeout') { steps {
      timeout(time: 8, unit: 'SECONDS') {
        sh '''
          . scripts/setenv
          make
        '''
      }
    } }
    stage('Test') {
      steps {
        sh '''
          . scripts/setenv
          ${K_BIN}/spawn-kserver
          make -C tests/unit-pass -j$(nproc) os-comparison
        '''
      }
      post {
        always {
          archiveArtifacts artifacts: 'tests/unit-pass/*config', allowEmptyArchive: true
        }
      }
    }
    stage('Test clean target') { steps {
      sh 'make clean'
      sh '[ $(git clean -xfd 2>&1 | wc -l) -eq 0 ]'
    } }
  }
}
