import type { Meta, StoryObj } from '@storybook/react';

import Application from "../components/Application";

// More on how to set up stories at: https://storybook.js.org/docs/react/writing-stories/introduction
const meta = {
  title: 'Example/FullApp',
  component: Application,
  tags: ['autodocs'],
} satisfies Meta<typeof Application>;

export default meta;
type Story = StoryObj<typeof meta>;
export const Primary: Story = {};
