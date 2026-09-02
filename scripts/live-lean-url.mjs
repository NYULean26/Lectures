#!/usr/bin/env node

import fs from 'node:fs'
import process from 'node:process'
import LZString from 'lz-string'

const liveLeanBaseUrl = 'https://live.lean-lang.org/'

function fixedEncodeURIComponent(value) {
  return encodeURIComponent(value).replace(/[()]/gu, (character) =>
    `%${character.codePointAt(0).toString(16)}`,
  )
}

export function buildLiveLeanUrl(code, project) {
  const codez = LZString.compressToBase64(code).replace(/=*$/u, '')
  const arguments_ = project === undefined ? { codez } : { project, codez }
  const hash = Object.entries(arguments_)
    .map(([key, value]) => `${key}=${fixedEncodeURIComponent(value)}`)
    .join('&')
  return `${liveLeanBaseUrl}#${hash}`
}

export function decodeLiveLeanUrl(url) {
  const hash = new URL(url).hash.slice(1)
  const arguments_ = Object.fromEntries(
    hash.split('&').map((argument) => {
      const separator = argument.indexOf('=')
      if (separator < 0) return [argument, '']
      return [
        argument.slice(0, separator),
        decodeURIComponent(argument.slice(separator + 1)),
      ]
    }),
  )

  if (arguments_.codez !== undefined) {
    const code = LZString.decompressFromBase64(arguments_.codez)
    if (code === null) throw new Error('The codez payload is not valid LZ-string data.')
    return code
  }
  if (arguments_.code !== undefined) return arguments_.code
  throw new Error('The URL has neither a codez nor a code argument.')
}

function usage() {
  console.error(
    'Usage:\n' +
      '  npm run live-url -- [--project PROJECT] FILE.lean\n' +
      '  npm run live-url -- --decode URL',
  )
}

function main(arguments_) {
  if (arguments_[0] === '--decode') {
    if (arguments_.length !== 2) {
      usage()
      return 2
    }
    process.stdout.write(decodeLiveLeanUrl(arguments_[1]))
    return 0
  }

  let project
  const projectIndex = arguments_.indexOf('--project')
  if (projectIndex >= 0) {
    if (arguments_[projectIndex + 1] === undefined) {
      usage()
      return 2
    }
    project = arguments_[projectIndex + 1]
    arguments_.splice(projectIndex, 2)
  }
  if (arguments_.length !== 1) {
    usage()
    return 2
  }

  const code = fs.readFileSync(arguments_[0], 'utf8')
  console.log(buildLiveLeanUrl(code, project))
  return 0
}

process.exitCode = main(process.argv.slice(2))
